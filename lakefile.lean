import Lake
open System Lake DSL

def cDir : FilePath := "c"
def libDir : FilePath := "lib"
def buildDir := defaultBuildDir

def ffiOTarget (pkgDir srcPath : FilePath) (compiler: FilePath) (deps : List FileTarget) (opts : Array String) : FileTarget :=
  let oFile := pkgDir / buildDir / srcPath.withExtension "o"
  let src := pkgDir / srcPath
  fileTargetWithDepList oFile ((inputFileTarget <| src) :: deps) fun _ => do
    compileO oFile src opts compiler

def includeFlag (path:FilePath) : String := "-I" ++ path.toString

def bindingsTarget (pkgDir : FilePath) : FileTarget  :=
  let oFile := pkgDir / buildDir / cDir / "bindings.o"
  let srcTarget := inputFileTarget <| pkgDir / cDir / "bindings.cpp"
  fileTargetWithDep oFile srcTarget fun srcFile => do
    IO.println $ "Lean: " ++ (← getLeanIncludeDir).toString
    compileO oFile srcFile
      #["-O3",
        "-DKATNUM=10",
        includeFlag (pkgDir / cDir / "openssl" / "include"),
        includeFlag (pkgDir / cDir / "keccak" / "include"),
        includeFlag (pkgDir / cDir / "mceliece348864"),
        includeFlag (← getLeanIncludeDir)]
      "c++"

def mcelieceFiles : Array FilePath :=
  #[ "gf.c", "util.c" ]

def mcelieceTarget (pkgDir : FilePath) (srcPath : FilePath) : FileTarget :=
  let src := cDir / "mceliece348864" / srcPath
  ffiOTarget pkgDir src "cc" []
     #["-O3",
       "-DKATNUM=10",
       "-DCRYPTO_NAMESPACE(x)=x",
       includeFlag (pkgDir / cDir / "mceliece348864"),
--       includeFlag "/usr/local/Cellar/openssl@1.1/1.1.1l_1/include",
       includeFlag (pkgDir / cDir / "keccak" / "include"),
       includeFlag (pkgDir / cDir / "openssl" / "include")
       ]

extern_lib libmceliece348864 :=
  let libFile := __dir__ / buildDir / libDir / "libmceliece348864.a"
  let dependencies := mcelieceFiles.map (mcelieceTarget __dir__)
  staticLibTarget libFile (dependencies ++ [bindingsTarget __dir__])

def keccakFiles : Array FilePath :=
  let base : FilePath := "keccak"
  #[ base / "Modes" / "SimpleFIPS202.c",
     base / "Constructions" / "KeccakSponge.c",
     base / "SnP" / "KeccakP-200"  / "Reference" / "KeccakP-200-reference.c",
     base / "SnP" / "KeccakP-400"  / "Reference" / "KeccakP-400-reference.c",
     base / "SnP" / "KeccakP-800"  / "Reference" / "KeccakP-800-reference.c",
     base / "SnP" / "KeccakP-1600" / "Reference" / "KeccakP-1600-reference.c"
   ]

def keccakTarget (pkgDir : FilePath) (srcPath : FilePath) : FileTarget :=
  let src := cDir / srcPath
  let commonIncPath := pkgDir / cDir / "keccak" / "Common"
  let incPath := pkgDir / cDir / "keccak" / "include" / "libkeccak.a.headers"
  ffiOTarget pkgDir src "cc" [] #["-O3", includeFlag incPath, includeFlag commonIncPath ]

extern_lib libkeccak :=
  let libFile := __dir__ / buildDir / libDir / "libkeccak.a"
  let dependencies := keccakFiles.map (keccakTarget __dir__)
  staticLibTarget libFile dependencies

--"-arch x86_64",

def opensslDefFlags : Array String :=
    #["-O3",
      "-Wall"
    ]

def opensslTarget (pkgDir : FilePath) (srcPath : FilePath) (extraOps : optParam (Array String) #[]) : FileTarget :=
  let src := cDir / srcPath
  let rootPath := includeFlag $ pkgDir / cDir / "openssl"
  let incPath := includeFlag $ pkgDir / cDir / "openssl" / "include"
  ffiOTarget pkgDir src "cc" [] (opensslDefFlags ++ #[incPath, rootPath] ++ extraOps)
--      -DENGINESDIR="\"/usr/local/lib/engines-1.1\"" -D_REENTRANT -DNDEBUG  -MMD -MF crypto/cryptlib.d.tmp -MT crypto/cryptlib.o -c -o crypto/cryptlib.o crypto/cryptlib.c


def opensslTargets (pkgDir : FilePath) : Array FileTarget :=
  let base : FilePath := "openssl"
  #[
     opensslTarget pkgDir $ base / "crypto" / "aes" / "aes_core.c"
   ]

extern_lib libcrypto :=
  let libFile := __dir__ / buildDir / libDir / "libcrypto.a"
  let dependencies := opensslTargets __dir__
  staticLibTarget libFile dependencies

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"@"7da24c4024a2cb547d9d6e85943027daa77d850f"

require smt from git
  "https://github.com/Vtec234/lean-smt"@"specialize-def"

package LeanCrypto where
  -- customize layout
  srcDir := "lib"
  libRoots := #[`Crypto]
  moreLeancArgs := #["-O3"]
  -- Setting this to `true` produces `libCrypto` which conflicts on case-insensitive filesystems
  -- with `libcrypto` produced from OpenSSL.
  precompileModules := false

lean_lib LeanCrypto where
  roots := #[`Crypto]

@[defaultTarget]
lean_exe mceliece where
  root := `McEliece

script runTest (args) do
  let some fname := args[0]? | do printUsage; return 1
  let fname := FilePath.mk fname
  if fname.extension != some "lean" then printUsage; return 1
  -- Note: this only works on Unix since it needs the shared library `libSmt`
  -- to also load its transitive dependencies.
  let smtDynlib := (← findModule? `Smt).get!.dynlibFile
  let out ← IO.Process.output {
    cmd := (← getLean).toString
    args := #[s!"--load-dynlib={smtDynlib}", fname.toString],
    env := (← getAugmentedEnv)
  }
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
