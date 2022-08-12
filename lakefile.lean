import Lake
open System Lake DSL

def cDir : FilePath := __dir__ / "c"
def buildDir := __dir__ / defaultBuildDir
def buildCDir := buildDir / "c"
def buildLibDir := buildDir / "lib"

package LeanCrypto where
  -- customize layout
  srcDir := "lib"
  moreLeancArgs := #["-O3"]
  -- Setting this to `true` produces `libCrypto` which conflicts on case-insensitive filesystems
  -- with `libcrypto` produced from OpenSSL.
  precompileModules := false

/-- Given a source path relative to `cDir`, build the corresponding `.o` in `buildCDir`. -/
def ffiOTarget (srcPath : FilePath) (compiler: FilePath) (deps : List (BuildJob FilePath))
    (opts : Array String) : IndexBuildM (BuildJob FilePath) := do
  let oFile := buildCDir / srcPath.withExtension "o"
  let src := cDir / srcPath
  buildFileAfterDepList oFile ((← inputFile src) :: deps) fun _ => do
    compileO oFile.toString oFile src opts compiler

def includeFlag (path:FilePath) : String := "-I" ++ path.toString

target bindingsTarget : FilePath := do
  -- IO.println $ "Lean: " ++ (← getLeanIncludeDir).toString
  ffiOTarget "bindings.cpp" "c++" []
    #["-O3",
      "-DKATNUM=10",
      includeFlag (cDir / "openssl" / "include"),
      includeFlag (cDir / "keccak" / "include"),
      includeFlag (cDir / "mceliece348864"),
      includeFlag (← getLeanIncludeDir)]

def mcelieceFiles : Array FilePath :=
  #[ "gf.c", "util.c" ]

def mcelieceTarget (srcPath : FilePath) : IndexBuildM (BuildJob FilePath) :=
  let src := "mceliece348864" / srcPath
  ffiOTarget src "cc" []
     #["-O3",
       "-DKATNUM=10",
       "-DCRYPTO_NAMESPACE(x)=x",
       includeFlag (cDir / "mceliece348864"),
--       includeFlag "/usr/local/Cellar/openssl@1.1/1.1.1l_1/include",
       includeFlag (cDir / "keccak" / "include"),
       includeFlag (cDir / "openssl" / "include")]

extern_lib libmceliece348864 (pkg : Package) := do
  let libFile := buildLibDir / "libmceliece348864.a"
  let dependencies ← mcelieceFiles.mapM mcelieceTarget
  let bindings ← fetch (pkg.target ``bindingsTarget)
  buildStaticLib libFile (dependencies.push bindings)

def keccakFiles : Array FilePath :=
  let base : FilePath := "keccak"
  #[ base / "Modes" / "SimpleFIPS202.c",
     base / "Constructions" / "KeccakSponge.c",
     base / "SnP" / "KeccakP-200"  / "Reference" / "KeccakP-200-reference.c",
     base / "SnP" / "KeccakP-400"  / "Reference" / "KeccakP-400-reference.c",
     base / "SnP" / "KeccakP-800"  / "Reference" / "KeccakP-800-reference.c",
     base / "SnP" / "KeccakP-1600" / "Reference" / "KeccakP-1600-reference.c"
   ]

def keccakTarget (srcPath : FilePath) : IndexBuildM (BuildJob FilePath) :=
  let commonIncPath := cDir / "keccak" / "Common"
  let incPath := cDir / "keccak" / "include" / "libkeccak.a.headers"
  ffiOTarget srcPath "cc" [] #["-O3", includeFlag incPath, includeFlag commonIncPath]

extern_lib libkeccak := do
  let libFile := buildLibDir / "libkeccak.a"
  let dependencies ← keccakFiles.mapM keccakTarget
  buildStaticLib libFile dependencies

--"-arch x86_64",

def opensslDefFlags : Array String :=
    #["-O3",
      "-Wall"
    ]

def opensslFiles : Array FilePath :=
  let base : FilePath := "openssl"
  #[ base / "crypto" / "aes" / "aes_core.c" ]

def opensslTarget (srcPath : FilePath) (extraOps : optParam (Array String) #[])
    : IndexBuildM (BuildJob FilePath) :=
  let rootPath := includeFlag $ cDir / "openssl"
  let incPath := includeFlag $ cDir / "openssl" / "include"
  ffiOTarget srcPath "cc" [] (opensslDefFlags ++ #[incPath, rootPath] ++ extraOps)
--      -DENGINESDIR="\"/usr/local/lib/engines-1.1\"" -D_REENTRANT -DNDEBUG  -MMD -MF crypto/cryptlib.d.tmp -MT crypto/cryptlib.o -c -o crypto/cryptlib.o crypto/cryptlib.c

extern_lib libcrypto := do
  let libFile :=  buildLibDir / "libcrypto.a"
  let dependencies ← opensslFiles.mapM opensslTarget
  buildStaticLib libFile dependencies

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"@"cf2e683c25eba2d798b2460d5703a63db72272c0"

require smt from git
  "https://github.com/ufmg-smite/lean-smt"@"main"

lean_lib LeanCrypto where
  roots := #[`Crypto]

@[defaultTarget]
lean_exe mceliece where
  root := `McEliece

def getTestOutput (fname : FilePath) : ScriptM IO.Process.Output := do
  -- Note: this only works on Unix since it needs the shared library `libSmt`
  -- to also load its transitive dependencies.
  let smtDynlib := (← findModule? `Smt).get!.dynlibFile
  IO.Process.output {
    cmd := (← getLean).toString
    args := #[s!"--load-dynlib={smtDynlib}", fname.toString],
    env := (← getAugmentedEnv)
  }

script runTest (args) do
  let some fname := args[0]? | do printUsage; return 1
  let fname := FilePath.mk fname
  if fname.extension != some "lean" then printUsage; return 1
  let out ← getTestOutput fname
  let expected ← IO.FS.readFile (fname.withExtension "expected")
  if ¬out.stderr.isEmpty ∨ out.stdout ≠ expected then
    IO.println s!"Stderr:\n{out.stderr}"
    IO.println s!"Stdout:\n{out.stdout}"
    IO.println s!"Expected:\n{expected}"
    return 2
  return 0

where printUsage : ScriptM Unit := do
  IO.println "Run a test file `test.lean` and compare the output to `test.expected`.

USAGE:
  lake run runTest <file>.lean"

script updateTest (args) do
  let some fname := args[0]? | do printUsage; return 1
  let fname := FilePath.mk fname
  if fname.extension != some "lean" then printUsage; return 1
  let out ← getTestOutput fname
  IO.FS.writeFile (fname.withExtension "expected") out.stdout
  return 0

where printUsage : ScriptM Unit := do
  IO.println "Run a test file `test.lean` and write the output to `test.expected`.

USAGE:
  lake run updateTest <file>.lean"
