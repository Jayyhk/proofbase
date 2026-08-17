import json
import os
import signal
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent # repo root
COMPILE_ENV = ROOT / "compile-env"
EXTRACTOR = COMPILE_ENV / "extract.lean"
ELAN_BIN = str(Path.home() / ".elan" / "bin")
TIMEOUT = 300 # compile timeout, seconds


# no extra behavior except subclassing Exception so we can raise CompileError
class CompileError(Exception):
    pass


# get supported lean versions by the directory version names that exist
def supported_versions():
    dirs = (p.name for p in COMPILE_ENV.iterdir() if (p / "lean-toolchain").exists())
    return sorted(dirs, key=lambda v: [int(x) for x in v.split(".")], reverse=True)


# run a command with lean toolchain on PATH and returns its result
def run(args, cwd):
    # copy env vars and put elan's bin dir on PATH so lake/lean are found
    env = {**os.environ, "PATH": ELAN_BIN + os.pathsep + os.environ.get("PATH", "")}

    proc = subprocess.Popen( # start command
        args, cwd=cwd, env=env, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True
    )
    try:
        out, err = proc.communicate(timeout=TIMEOUT) # finish and collect output, give up after TIMEOUT seconds
    except subprocess.TimeoutExpired: # ran too long, try to kill it
        try:
            os.killpg(os.getpgid(proc.pid), signal.SIGKILL) # try to kill whole process group
        except ProcessLookupError:
            pass # nothing to do, already exited
        proc.communicate() # collect whatever's left and let the OS clean up dead process
        raise CompileError(f"compilation timed out after {TIMEOUT // 60} minutes")

    return subprocess.CompletedProcess(args, proc.returncode, out, err) # finished in time


# drop lake's "trace:" lines
def clean_output(result):
    lines = [l for l in (result.stdout + result.stderr).splitlines() if not l.startswith("trace:")]
    return "\n".join(lines).strip()


# write the proof, compile it, run the extractor, return graph json
def compile_and_extract(file, version):
    env_dir = COMPILE_ENV / version # lean version dir
    upload = env_dir / "Upload.lean"
    out = env_dir / ".upload.json"
    upload.write_text(file) # write the uploaded proof into Upload.lean

    build = run(["lake", "build", "Upload"], env_dir) # compile the proof
    if build.returncode != 0:
        raise CompileError(clean_output(build))

    extract = run(["lake", "env", "lean", "--run", str(EXTRACTOR), "-o", str(out), "Upload"], env_dir) # extract info from .olean files
    if extract.returncode != 0:
        raise CompileError(clean_output(extract))

    return json.loads(out.read_text()) # parse json the extractor wrote
