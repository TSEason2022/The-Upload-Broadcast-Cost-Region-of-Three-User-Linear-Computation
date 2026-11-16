"""Public API, resource controls, v1 migration and v2 provenance regression tests."""
from __future__ import annotations

import contextlib
import copy
import io
import json
import tempfile
import threading
import unittest
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from unittest.mock import patch

from three_user_codes import (
    BlocklengthError, CodingError, CompilationCancelled, Field, InputFormatError,
    Matrix, ReadLimits, SearchBudgetExceeded, Task, VerificationError,
    compile_task, load_code, load_task, resonant_task, save_code, save_task, task_fingerprint,
)
from three_user_codes.cli import main
from three_user_codes.io import loads_json, result_from_dict, result_to_dict, task_from_dict, write_json
from three_user_codes.linalg import eye, zeros
from three_user_codes.progress import SearchBudget


class LibraryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.task=resonant_task(Field(3),1)
        cls.result=compile_task(cls.task)

    def test_task_from_rows(self):
        t=Task.from_rows(3,[a.rows for a in self.task.original_side],[w.rows for w in self.task.original_demand])
        self.assertEqual(t,self.task)
        self.assertEqual(task_fingerprint(t),task_fingerprint(self.task))
        with self.assertRaises(ValueError): Task.from_rows(3,[[],[],[]],[[],[],[]])
        self.assertEqual(Task.from_rows(3,[[],[],[]],[[],[],[]],n=0).n,0)
        with self.assertRaises(TypeError): Task.from_rows(True,[[],[],[]],[[],[],[]],n=0)

    def test_public_io_roundtrip(self):
        with tempfile.TemporaryDirectory() as directory:
            task=Path(directory)/'task.json';code=Path(directory)/'code.json'
            save_task(self.task,task);save_code(self.result,self.task,code)
            loaded=load_task(task)
            result,original=load_code(code,expected_fingerprint=task_fingerprint(loaded))
            self.assertTrue(result.verify(original))
            self.assertEqual(original,self.task)
            self.assertEqual(result.input_fingerprint,task_fingerprint(self.task))

    def test_duplicate_original_row_now_rejected(self):
        data=result_to_dict(self.result,self.task)
        data['input_task']['side'][0].append(data['input_task']['side'][0][0])
        with self.assertRaises(VerificationError): result_from_dict(data)

    def test_original_row_reordering_now_rejected(self):
        data=result_to_dict(self.result,self.task)
        data['input_task']['side'][0].reverse()
        with self.assertRaises(VerificationError): result_from_dict(data)

    def test_direct_result_representation_binding(self):
        a=self.task.original_side
        changed=Task(self.task.field,(Matrix(self.task.field,a[0].rows+(a[0].rows[0],)),a[1],a[2]),self.task.original_demand)
        self.assertEqual(changed,self.task) # mathematical task unchanged
        with self.assertRaises(VerificationError): self.result.verify(changed)
        with self.assertRaises(VerificationError): self.result.operating_code(changed)

    def test_embedded_digest_is_not_authentication(self):
        data=result_to_dict(self.result,self.task)
        old=data['input_fingerprint']
        data['input_task']['side'][0].append(data['input_task']['side'][0][0])
        data['input_fingerprint']=task_fingerprint(task_from_dict(data['input_task']))
        result_from_dict(data) # a digest can be recomputed; document honestly
        with self.assertRaises(VerificationError): result_from_dict(data,expected_fingerprint=old)

    def test_legacy_v1_policy_and_migration(self):
        data=result_to_dict(self.result,self.task)
        data['schema']='three-user-compiled-code-v1';data.pop('input_fingerprint')
        result,task=result_from_dict(data)
        self.assertIsNone(result.input_fingerprint)
        with self.assertRaises(InputFormatError): result_from_dict(data,allow_legacy=False)
        self.assertEqual(result_to_dict(result,task)['schema'],'three-user-compiled-code-v2')

    def test_current_examples_compile_and_roundtrip(self):
        root=Path(__file__).resolve().parents[1]
        for name in ('resonant_binary.json', 'extension_field.json',
                     'integer_cycle_mix.json'):
            task=load_task(root/'examples'/name)
            compiled=compile_task(task)
            result,task=result_from_dict(result_to_dict(compiled,task))
            self.assertTrue(result.verify(task))

    def test_strict_json_numbers_and_duplicates(self):
        for text in ('{"x":NaN}','{"x":Infinity}','{"x":1e9999}','{"x":-1e9999}','{"x":1,"x":2}'):
            with self.assertRaises(InputFormatError): loads_json(text)
        self.assertEqual(loads_json('{"elapsed":1.25}')['elapsed'],1.25)

    def test_json_size_and_depth_limits(self):
        with self.assertRaises(InputFormatError): loads_json(' '*100,limits=ReadLimits(max_bytes=16))
        with self.assertRaises(InputFormatError): loads_json('['*10000+']'*10000)
        with self.assertRaises(InputFormatError): loads_json(b'\xff')
        with self.assertRaises(ValueError): ReadLimits(max_bytes=True)

    def test_shape_limits_before_algebra(self):
        data=result_to_dict(self.result,self.task)
        with self.assertRaises(InputFormatError): result_from_dict(data,limits=ReadLimits(max_cells=10))
        data['certificate']['blocklength']=10**12
        with self.assertRaises(InputFormatError): result_from_dict(data)

    def test_metadata_mismatch_rejected_before_lifting(self):
        data=result_to_dict(self.result,self.task)
        data['certificate']['blocklength']=3
        with self.assertRaises(VerificationError): result_from_dict(data)

    def test_atomic_serialization_failure_retains_old_file(self):
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'x.json';path.write_text('old')
            with self.assertRaises(ValueError): write_json(path,{'x':float('nan')})
            self.assertEqual(path.read_text(),'old')
            self.assertEqual([p.name for p in path.parent.iterdir()],['x.json'])

    def test_progress_and_phase_timings(self):
        events=[]
        result=compile_task(self.task,progress=events.append)
        self.assertEqual(events[-1].stage,'completed')
        self.assertIn('bounds',[e.stage for e in events])
        self.assertTrue(all(a.elapsed_seconds<=b.elapsed_seconds for a,b in zip(events,events[1:])))
        self.assertIn('certificate',result.stats['stage_seconds'])
        with self.assertRaises(AttributeError): events[-1].stage='bad'

    def test_pre_cancelled(self):
        event=threading.Event();event.set()
        with self.assertRaises(CompilationCancelled): compile_task(self.task,cancel_event=event)
        self.assertEqual(eye(Field(3),2)@eye(Field(3),2),eye(Field(3),2))

    def test_cancel_during_stage_and_context_cleanup(self):
        event=threading.Event()
        def callback(progress):
            if progress.stage=='broadcast':event.set()
        with self.assertRaises(CompilationCancelled): compile_task(self.task,cancel_event=event,progress=callback)
        self.assertTrue(compile_task(self.task).certificate.verify())

    def test_callback_errors_propagate(self):
        class CallbackError(Exception): pass
        def callback(event): raise CallbackError('callback failed')
        with self.assertRaises(CallbackError): compile_task(self.task,progress=callback)

    def test_nested_compile_context_is_restored(self):
        nested=[]
        def callback(event):
            if event.stage=='bounds' and not nested:
                nested.append(compile_task(self.task))
        outer=compile_task(self.task,progress=callback)
        self.assertEqual(outer.certificate.signal,nested[0].certificate.signal)

    def test_time_budget_includes_bounds_and_callbacks(self):
        with self.assertRaises(SearchBudgetExceeded): compile_task(self.task,max_seconds=1e-30)
        budget=SearchBudget(None,1)
        budget.start=0.0
        with patch('three_user_codes.progress.monotonic',return_value=2):
            with self.assertRaises(SearchBudgetExceeded): budget.check()

    def test_state_budget_not_infeasibility(self):
        budget=SearchBudget(1,None)
        budget.tick()
        with self.assertRaises(SearchBudgetExceeded) as raised:budget.tick()
        self.assertEqual(raised.exception.stats['states'],2)
        self.assertIsInstance(raised.exception,CodingError)

    def test_option_validation(self):
        for value in (True,-1,1.0,'3'):
            with self.assertRaises(ValueError):compile_task(self.task,max_cache_entries=value)
        for value in (-1,True,float('nan')):
            with self.assertRaises(ValueError):compile_task(self.task,progress_interval=value)
        with self.assertRaises(TypeError):compile_task(self.task,cancel_event=object())
        with self.assertRaises(TypeError):compile_task(self.task,progress=42)
        with self.assertRaises(BlocklengthError):compile_task(self.task,force_blocklength=1)

    def test_concurrent_compile_results(self):
        with ThreadPoolExecutor(max_workers=4) as executor:
            results=list(executor.map(lambda _:compile_task(self.task),range(8)))
        self.assertTrue(all(r.certificate.signal==results[0].certificate.signal for r in results))

    def test_cache_disabled_preserves_result(self):
        for n in (1,2):
            task=resonant_task(Field(3),n)
            a=compile_task(task,fast_paths=False,max_cache_entries=0)
            b=compile_task(task,fast_paths=False,max_cache_entries=2048)
            self.assertEqual(a.certificate.to_dict(),b.certificate.to_dict())

    def test_batched_streaming_runtime(self):
        code=self.result.operating_code(self.task)
        n=code.certificate.task.n
        source=Matrix(self.task.field,[[i%3,(i+1)%3] for i in range(n)])
        observations=tuple(a@source for a in code.original_side)
        output=code.execute(observations)
        self.assertEqual(output.decoded,tuple(w@source for w in code.original_demand))
        seen=[]
        def batches():
            for i in range(3):
                seen.append(i);yield observations
        iterator=code.iter_execute(batches())
        self.assertEqual(seen,[])
        self.assertEqual(next(iterator),output)
        self.assertEqual(seen,[0])
        self.assertEqual(list(iterator),[output,output])

    def test_cli_forced_scalar_is_json_not_traceback(self):
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'task.json';save_task(self.task,path)
            err=io.StringIO()
            with contextlib.redirect_stderr(err):status=main(['compile',str(path),'--force-working-blocklength','1'])
            self.assertEqual(status,2)
            self.assertEqual(json.loads(err.getvalue())['status'],'error')
            self.assertNotIn('Traceback',err.getvalue())

    def test_cli_progress_is_stderr_only(self):
        with tempfile.TemporaryDirectory() as directory:
            out,err=io.StringIO(),io.StringIO()
            with contextlib.redirect_stdout(out),contextlib.redirect_stderr(err):
                status=main(['demo','--q','3','--progress','--output',str(Path(directory)/'code.json')])
            self.assertEqual(status,0)
            self.assertEqual(json.loads(out.getvalue())['status'],'verified')
            self.assertTrue(all(json.loads(line)['status']=='progress' for line in err.getvalue().splitlines()))

    def test_cli_internal_errors_are_distinct(self):
        from three_user_codes.errors import ConstructionError
        err=io.StringIO()
        with patch('three_user_codes.cli.compile_task',side_effect=ConstructionError('invariant')),contextlib.redirect_stderr(err):
            status=main(['demo'])
        self.assertEqual(status,1)
        self.assertEqual(json.loads(err.getvalue())['status'],'construction_error')

    def test_zero_source_and_zero_sample_batches(self):
        task=Task.from_rows(3,[[],[],[]],[[],[],[]],n=0)
        result=compile_task(task)
        code=result.operating_code(task)
        self.assertEqual(code.execute((zeros(task.field,0,0),)*3).decoded,(zeros(task.field,0,0),)*3)


if __name__=='__main__': unittest.main()
