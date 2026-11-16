"""Install the package, then run: python examples/quickstart.py"""
from pathlib import Path
from tempfile import TemporaryDirectory

from three_user_codes import Field, Matrix, Task, compile_task, load_code, save_code


def main():
    field=Field(3)
    task=Task.from_rows(field,
        [[[1,0]],[[0,1]],[[1,1]]],
        [[[0,1]],[[1,0]],[[1,0]]],n=2)
    result=compile_task(task,max_states=100_000,max_seconds=30)
    code=result.operating_code(task)
    # Simulation only: real encoders receive observations, never source.
    source=Matrix(field,[[i%3,(i+1)%3] for i in range(code.certificate.task.n)])
    observations=tuple(a@source for a in code.original_side)
    execution=code.execute(observations)
    assert execution.decoded==tuple(w@source for w in code.original_demand)
    with TemporaryDirectory() as directory:
        path=Path(directory)/'code.json'
        save_code(result,task,path)
        restored,original=load_code(path,expected_fingerprint=result.input_fingerprint)
        restored.verify(original)
    print('exact rates:',result.upload_optimum,result.broadcast_optimum)
    print('blocklength:',result.certificate.blocklength)
    print('decoded:',[m.to_list() for m in execution.decoded])


if __name__=='__main__':main()
