"""Downstream public API type smoke example; not an exhaustive internal audit."""
from three_user_codes import (
    CompileResult, ExecutionResult, Field, Matrix, OperatingCode,
    ProgressEvent, Task, compile_task,
)


def example() -> None:
    field = Field(3)
    task: Task = Task.from_rows(
        field,
        [[[1, 0]], [[0, 1]], [[1, 1]]],
        [[[0, 1]], [[1, 0]], [[1, 0]]],
        n=2,
    )
    events: list[ProgressEvent] = []
    result: CompileResult = compile_task(task, progress=events.append)
    code: OperatingCode = result.operating_code(task)
    source = Matrix(field, [[1] for _ in range(code.certificate.task.n)])
    observations = tuple(a @ source for a in code.original_side)
    execution: ExecutionResult = code.execute(observations)
    outputs: tuple[Matrix, Matrix, Matrix] = execution.decoded
    assert len(outputs) == 3
