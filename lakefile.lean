import Lake
open System Lake DSL

def cDir : FilePath := "c"
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
  #[ "benes.c", "bm.c", "controlbits.c", "decrypt.c", "encrypt.c", "gf.c",
     "pk_gen.c", "root.c", "sk_gen.c", "synd.c", "transpose.c", "util.c"
    ]

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
  let libFile := __dir__ / buildDir / cDir / "libmceliece348864.a"
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
  let libFile := __dir__ / buildDir / cDir / "libkeccak.a"
  let dependencies := keccakFiles.map (keccakTarget __dir__)
  staticLibTarget libFile dependencies

--"-arch x86_64",

def opensslDefFlags : Array String :=
    #["-O3",
      "-Wall",
      "-DL_ENDIAN",
      "-DOPENSSL_PIC",
      "-DOPENSSL_CPUID_OBJ",
      "-DOPENSSL_IA32_SSE2",
      "-DOPENSSL_BN_ASM_MONT",
      "-DOPENSSL_BN_ASM_MONT5",
      "-DOPENSSL_BN_ASM_GF2m",
      "-DOPENSSL_NO_ARIA",
      "-DOPENSSL_NO_BF",
      "-DOPENSSL_NO_BLAKE2",
      "-DOPENSSL_NO_CAMELLIA",
      "-DOPENSSL_NO_CAST",
      "-DOPENSSL_NO_CHACHA",
      "-DOPENSSL_NO_CT",
      "-DOPENSSL_NO_DES",
      "-DOPENSSL_NO_DSA",
      "-DOPENSSL_NO_ENGINE",
      "-DOPENSSL_NO_EC",
      "-DOPENSSL_NO_ERR",
      "-DOPENSSL_NO_IDEA",
      "-DOPENSSL_NO_MD4",
      -- "-DOPENSSL_NO_MD5",
      "-DOPENSSL_NO_OCB",
      "-DOPENSSL_NO_RC2",
      "-DOPENSSL_NO_RC4",
      "-DOPENSSL_NO_RC5",
      "-DPENSSL_NO_RMD160",
      "-DOPENSSL_NO_RSA",
      "-DOPENSSL_NO_SCRYPT",
      "-DOPENSSL_NO_SEED",
      "-DOPENSSL_NO_SIPHASH",
      "-DOPENSSL_NO_SM2",
      "-DOPENSSL_NO_SM3",
      "-DOPENSSL_NO_SM4",
      "-DOPENSSL_NO_WHIRLPOOL",
      "-DSHA1_ASM",
      "-DSHA256_ASM",
      "-DSHA512_ASM",
      "-DKECCAK1600_ASM",
      "-DRC4_ASM",
      "-DMD5_ASM",
      "-DAESNI_ASM",
      "-DVPAES_ASM",
      "-DGHASH_ASM",
      "-DECP_NISTZ256_ASM",
      "-DX25519_ASM",
      "-DPOLY1305_ASM",
      "-DOPENSSLDIR=\"/usr/local/ssl\""
    ]

def opensslTarget (pkgDir : FilePath) (srcPath : FilePath) (extraOps : optParam (Array String) #[]) : FileTarget :=
  let src := cDir / srcPath
  let rootPath := includeFlag $ pkgDir / cDir / "openssl"
  let incPath := includeFlag $ pkgDir / cDir / "openssl" / "include"
  ffiOTarget pkgDir src "cc" [] (opensslDefFlags ++ #[incPath, rootPath] ++ extraOps)
--      -DENGINESDIR="\"/usr/local/lib/engines-1.1\"" -D_REENTRANT -DNDEBUG  -MMD -MF crypto/cryptlib.d.tmp -MT crypto/cryptlib.o -c -o crypto/cryptlib.o crypto/cryptlib.c


def opensslTargets (pkgDir : FilePath) : Array FileTarget :=
  let base : FilePath := "openssl"
  let modesPath := includeFlag $ pkgDir / cDir / "openssl" / "crypto" / "modes"
  let ocspPath := includeFlag $ pkgDir / cDir / "openssl" / "crypto" / "ocsp"
  #[ opensslTarget pkgDir $ base / "crypto" / "cryptlib.c",
     opensslTarget pkgDir $ base / "crypto" / "ctype.c",
     opensslTarget pkgDir $ base / "crypto" / "ex_data.c",
     opensslTarget pkgDir $ base / "crypto" / "getenv.c",
     opensslTarget pkgDir $ base / "crypto" / "init.c",
     opensslTarget pkgDir $ base / "crypto" / "lhash"/ "lhash.c",
     opensslTarget pkgDir $ base / "crypto" / "mem.c",
     opensslTarget pkgDir $ base / "crypto" / "mem_dbg.c",
     opensslTarget pkgDir $ base / "crypto" / "mem_sec.c",
     opensslTarget pkgDir $ base / "crypto" / "o_dir.c",
     opensslTarget pkgDir $ base / "crypto" / "o_fopen.c",
     opensslTarget pkgDir $ base / "crypto" / "o_str.c",
     opensslTarget pkgDir $ base / "crypto" / "o_time.c",
     opensslTarget pkgDir $ base / "crypto" / "threads_pthread.c",
     opensslTarget pkgDir $ base / "crypto" / "uid.c",
     opensslTarget pkgDir $ base / "crypto" / "x86_64cpuid.s",
     opensslTarget pkgDir $ base / "crypto" / "aes" / "aes_cbc.c",
     opensslTarget pkgDir $ base / "crypto" / "aes" / "aes_core.c",
     opensslTarget pkgDir $ base / "crypto" / "aes" / "aes_wrap.c",
     opensslTarget pkgDir $ base / "crypto" / "aes" / "aesni-mb-x86_64.s",
     opensslTarget pkgDir $ base / "crypto" / "aes" / "aesni-sha1-x86_64.s",
     opensslTarget pkgDir $ base / "crypto" / "aes" / "aesni-sha256-x86_64.s",
     opensslTarget pkgDir $ base / "crypto" / "aes" / "aesni-x86_64.s",
     opensslTarget pkgDir $ base / "crypto" / "aes" / "vpaes-x86_64.s",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "a_bitstr.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "a_d2i_fp.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "a_digest.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "a_dup.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "a_gentm.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "a_i2d_fp.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "a_int.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "a_mbstr.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "a_octet.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "a_object.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "a_print.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "a_sign.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "a_strex.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "a_strnid.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "a_time.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "a_type.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "a_utctm.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "a_utf8.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "a_verify.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "asn_mime.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "asn_moid.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "asn_mstbl.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "asn_pack.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "asn1_gen.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "asn1_lib.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "asn1_par.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "ameth_lib.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "bio_asn1.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "bio_ndef.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "d2i_pr.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "evp_asn1.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "f_int.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "f_string.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "i2d_pr.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "p5_pbe.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "p5_pbev2.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "p8_pkey.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "t_pkey.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "tasn_dec.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "tasn_enc.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "tasn_fre.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "tasn_new.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "tasn_prn.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "tasn_typ.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "tasn_utl.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "x_algor.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "x_bignum.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "x_int64.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "x_sig.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "x_spki.c",
     opensslTarget pkgDir $ base / "crypto" / "asn1" / "x_val.c",
     opensslTarget pkgDir $ base / "crypto" / "async" / "async.c",
     opensslTarget pkgDir $ base / "crypto" / "async" / "async_wait.c",
     opensslTarget pkgDir $ base / "crypto" / "async" / "arch" / "async_posix.c",
     opensslTarget pkgDir $ base / "crypto" / "bio" / "b_addr.c",
     opensslTarget pkgDir $ base / "crypto" / "bio" / "b_dump.c",
     opensslTarget pkgDir $ base / "crypto" / "bio" / "b_print.c",
     opensslTarget pkgDir $ base / "crypto" / "bio" / "b_sock.c",
     opensslTarget pkgDir $ base / "crypto" / "bio" / "b_sock2.c",
     opensslTarget pkgDir $ base / "crypto" / "bio" / "bf_buff.c",
     opensslTarget pkgDir $ base / "crypto" / "bio" / "bio_lib.c",
     opensslTarget pkgDir $ base / "crypto" / "bio" / "bio_meth.c",
     opensslTarget pkgDir $ base / "crypto" / "bio" / "bss_file.c",
     opensslTarget pkgDir $ base / "crypto" / "bio" / "bss_mem.c",
     opensslTarget pkgDir $ base / "crypto" / "bio" / "bss_null.c",
     opensslTarget pkgDir $ base / "crypto" / "bio" / "bss_sock.c",
     opensslTarget pkgDir $ base / "crypto" / "bn" / "bn_add.c",
     opensslTarget pkgDir $ base / "crypto" / "bn" / "bn_ctx.c",
     opensslTarget pkgDir $ base / "crypto" / "bn" / "bn_dh.c",
     opensslTarget pkgDir $ base / "crypto" / "bn" / "bn_div.c",
     opensslTarget pkgDir $ base / "crypto" / "bn" / "bn_exp.c",
     opensslTarget pkgDir $ base / "crypto" / "bn" / "bn_gcd.c",
     opensslTarget pkgDir $ base / "crypto" / "bn" / "bn_intern.c",
     opensslTarget pkgDir $ base / "crypto" / "bn" / "bn_lib.c",
     opensslTarget pkgDir $ base / "crypto" / "bn" / "bn_mod.c",
     opensslTarget pkgDir $ base / "crypto" / "bn" / "bn_mont.c",
     opensslTarget pkgDir $ base / "crypto" / "bn" / "bn_mul.c",
     opensslTarget pkgDir $ base / "crypto" / "bn" / "bn_prime.c",
     opensslTarget pkgDir $ base / "crypto" / "bn" / "bn_print.c",
     opensslTarget pkgDir $ base / "crypto" / "bn" / "bn_rand.c",
     opensslTarget pkgDir $ base / "crypto" / "bn" / "bn_recp.c",
     opensslTarget pkgDir $ base / "crypto" / "bn" / "bn_shift.c",
     opensslTarget pkgDir $ base / "crypto" / "bn" / "bn_sqr.c",
     opensslTarget pkgDir $ base / "crypto" / "bn" / "bn_word.c",
     opensslTarget pkgDir $ base / "crypto" / "bn" / "rsaz_exp.c",
     opensslTarget pkgDir $ base / "crypto" / "bn" / "rsaz-avx2.s",
     opensslTarget pkgDir $ base / "crypto" / "bn" / "rsaz-x86_64.s",
     opensslTarget pkgDir $ base / "crypto" / "bn" / "x86_64-mont.s",
     opensslTarget pkgDir $ base / "crypto" / "bn" / "x86_64-mont5.s",
     opensslTarget pkgDir $ base / "crypto" / "bn" / "asm" / "x86_64-gcc.c",
     opensslTarget pkgDir $ base / "crypto" / "buffer" / "buffer.c",
     opensslTarget pkgDir $ base / "crypto" / "cmac" / "cm_ameth.c",
     opensslTarget pkgDir $ base / "crypto" / "cmac" / "cm_pmeth.c",
     opensslTarget pkgDir $ base / "crypto" / "cmac" / "cmac.c",
     opensslTarget pkgDir $ base / "crypto" / "cms" / "cms_asn1.c",
     opensslTarget pkgDir $ base / "crypto" / "cms" / "cms_att.c",
     opensslTarget pkgDir $ base / "crypto" / "cms" / "cms_dd.c",
     opensslTarget pkgDir $ base / "crypto" / "cms" / "cms_enc.c",
     opensslTarget pkgDir $ base / "crypto" / "cms" / "cms_env.c",
     opensslTarget pkgDir $ base / "crypto" / "cms" / "cms_io.c",
     opensslTarget pkgDir $ base / "crypto" / "cms" / "cms_kari.c",
     opensslTarget pkgDir $ base / "crypto" / "cms" / "cms_lib.c",
     opensslTarget pkgDir $ base / "crypto" / "cms" / "cms_pwri.c",
     opensslTarget pkgDir $ base / "crypto" / "cms" / "cms_sd.c",
     opensslTarget pkgDir $ base / "crypto" / "comp" / "c_zlib.c",
     opensslTarget pkgDir $ base / "crypto" / "conf" / "conf_api.c",
     opensslTarget pkgDir $ base / "crypto" / "conf" / "conf_def.c",
     opensslTarget pkgDir $ base / "crypto" / "conf" / "conf_lib.c",
     opensslTarget pkgDir $ base / "crypto" / "conf" / "conf_mall.c",
     opensslTarget pkgDir $ base / "crypto" / "conf" / "conf_mod.c",
     opensslTarget pkgDir $ base / "crypto" / "conf" / "conf_sap.c",
     opensslTarget pkgDir $ base / "crypto" / "conf" / "conf_ssl.c",
     opensslTarget pkgDir $ base / "crypto" / "dh" / "dh_ameth.c",
     opensslTarget pkgDir $ base / "crypto" / "dh" / "dh_asn1.c",
     opensslTarget pkgDir $ base / "crypto" / "dh" / "dh_check.c",
     opensslTarget pkgDir $ base / "crypto" / "dh" / "dh_gen.c",
     opensslTarget pkgDir $ base / "crypto" / "dh" / "dh_kdf.c",
     opensslTarget pkgDir $ base / "crypto" / "dh" / "dh_key.c",
     opensslTarget pkgDir $ base / "crypto" / "dh" / "dh_lib.c",
     opensslTarget pkgDir $ base / "crypto" / "dh" / "dh_meth.c",
     opensslTarget pkgDir $ base / "crypto" / "dh" / "dh_pmeth.c",
     opensslTarget pkgDir $ base / "crypto" / "dh" / "dh_rfc5114.c",
     opensslTarget pkgDir $ base / "crypto" / "dh" / "dh_rfc7919.c",
     opensslTarget pkgDir $ base / "crypto" / "dso" / "dso_dlfcn.c",
     opensslTarget pkgDir $ base / "crypto" / "dso" / "dso_lib.c",
     opensslTarget pkgDir $ base / "crypto" / "err" / "err.c",
     opensslTarget pkgDir $ base / "crypto" / "err" / "err_all.c",
     opensslTarget pkgDir $ base / "crypto" / "err" / "err_prn.c",
     opensslTarget pkgDir ( base / "crypto" / "evp" / "bio_b64.c"),
     opensslTarget pkgDir ( base / "crypto" / "evp" / "bio_enc.c"),
     opensslTarget pkgDir ( base / "crypto" / "evp" / "bio_md.c"),
     opensslTarget pkgDir ( base / "crypto" / "evp" / "c_allc.c"),
     opensslTarget pkgDir ( base / "crypto" / "evp" / "c_alld.c"),
     opensslTarget pkgDir ( base / "crypto" / "evp" / "digest.c"),
     opensslTarget pkgDir ( base / "crypto" / "evp" / "e_aes.c") #[modesPath],
     opensslTarget pkgDir ( base / "crypto" / "evp" / "e_aes_cbc_hmac_sha1.c") #[modesPath],
     opensslTarget pkgDir ( base / "crypto" / "evp" / "e_aes_cbc_hmac_sha256.c") #[modesPath],
     opensslTarget pkgDir $ base / "crypto" / "evp" / "encode.c",
     opensslTarget pkgDir $ base / "crypto" / "evp" / "evp_cnf.c",
     opensslTarget pkgDir $ base / "crypto" / "evp" / "evp_enc.c",
     opensslTarget pkgDir $ base / "crypto" / "evp" / "evp_key.c",
     opensslTarget pkgDir $ base / "crypto" / "evp" / "evp_lib.c",
     opensslTarget pkgDir $ base / "crypto" / "evp" / "evp_pbe.c",
     opensslTarget pkgDir $ base / "crypto" / "evp" / "evp_pkey.c",
     opensslTarget pkgDir $ base / "crypto" / "evp" / "m_md5.c",
     opensslTarget pkgDir $ base / "crypto" / "evp" / "m_md5_sha1.c",
     opensslTarget pkgDir $ base / "crypto" / "evp" / "m_ripemd.c",
     opensslTarget pkgDir $ base / "crypto" / "evp" / "m_sha1.c",
     opensslTarget pkgDir $ base / "crypto" / "evp" / "m_sha3.c",
     opensslTarget pkgDir $ base / "crypto" / "evp" / "m_sigver.c",
     opensslTarget pkgDir $ base / "crypto" / "evp" / "names.c",
     opensslTarget pkgDir $ base / "crypto" / "evp" / "p_lib.c",
     opensslTarget pkgDir $ base / "crypto" / "evp" / "p_sign.c",
     opensslTarget pkgDir $ base / "crypto" / "evp" / "p_verify.c",
     opensslTarget pkgDir $ base / "crypto" / "evp" / "p5_crpt.c",
     opensslTarget pkgDir $ base / "crypto" / "evp" / "p5_crpt2.c",
     opensslTarget pkgDir $ base / "crypto" / "evp" / "pmeth_fn.c",
     opensslTarget pkgDir $ base / "crypto" / "evp" / "pmeth_gn.c",
     opensslTarget pkgDir $ base / "crypto" / "evp" / "pmeth_lib.c",
     opensslTarget pkgDir $ base / "crypto" / "hmac" / "hm_ameth.c",
     opensslTarget pkgDir $ base / "crypto" / "hmac" / "hm_pmeth.c",
     opensslTarget pkgDir $ base / "crypto" / "hmac" / "hmac.c",
     opensslTarget pkgDir $ base / "crypto" / "kdf" / "hkdf.c",
     opensslTarget pkgDir $ base / "crypto" / "kdf" / "tls1_prf.c",
     opensslTarget pkgDir $ base / "crypto" / "md5" / "md5_dgst.c",
     opensslTarget pkgDir $ base / "crypto" / "md5" / "md5-x86_64.s",
     opensslTarget pkgDir $ base / "crypto" / "modes" / "aesni-gcm-x86_64.s",
     opensslTarget pkgDir $ base / "crypto" / "modes" / "cbc128.c",
     opensslTarget pkgDir $ base / "crypto" / "modes" / "ccm128.c",
     opensslTarget pkgDir $ base / "crypto" / "modes" / "cfb128.c",
     opensslTarget pkgDir $ base / "crypto" / "modes" / "ctr128.c",
     opensslTarget pkgDir $ base / "crypto" / "modes" / "gcm128.c",
     opensslTarget pkgDir $ base / "crypto" / "modes" / "ghash-x86_64.s",
     opensslTarget pkgDir $ base / "crypto" / "modes" / "ofb128.c",
     opensslTarget pkgDir $ base / "crypto" / "modes" / "wrap128.c",
     opensslTarget pkgDir $ base / "crypto" / "modes" / "xts128.c",
     opensslTarget pkgDir $ base / "crypto" / "objects" / "o_names.c",
     opensslTarget pkgDir $ base / "crypto" / "objects" / "obj_dat.c",
     opensslTarget pkgDir $ base / "crypto" / "objects" / "obj_lib.c",
     opensslTarget pkgDir $ base / "crypto" / "objects" / "obj_xref.c",
     opensslTarget pkgDir $ base / "crypto" / "ocsp" / "ocsp_asn.c",
     opensslTarget pkgDir $ base / "crypto" / "ocsp" / "ocsp_ht.c",
     opensslTarget pkgDir $ base / "crypto" / "pem" / "pem_lib.c",
     opensslTarget pkgDir $ base / "crypto" / "pem" / "pem_oth.c",
     opensslTarget pkgDir $ base / "crypto" / "pkcs7" / "pk7_asn1.c",
     opensslTarget pkgDir $ base / "crypto" / "pkcs7" / "pk7_attr.c",
     opensslTarget pkgDir $ base / "crypto" / "pkcs7" / "pk7_doit.c",
     opensslTarget pkgDir $ base / "crypto" / "pkcs7" / "pk7_lib.c",
     opensslTarget pkgDir $ base / "crypto" / "pkcs12" / "p12_add.c",
     opensslTarget pkgDir $ base / "crypto" / "pkcs12" / "p12_asn.c",
     opensslTarget pkgDir $ base / "crypto" / "pkcs12" / "p12_attr.c",
     opensslTarget pkgDir $ base / "crypto" / "pkcs12" / "p12_crpt.c",
     opensslTarget pkgDir $ base / "crypto" / "pkcs12" / "p12_decr.c",
     opensslTarget pkgDir $ base / "crypto" / "pkcs12" / "p12_key.c",
     opensslTarget pkgDir $ base / "crypto" / "pkcs12" / "p12_kiss.c",
     opensslTarget pkgDir $ base / "crypto" / "pkcs12" / "p12_mutl.c",
     opensslTarget pkgDir $ base / "crypto" / "pkcs12" / "p12_p8d.c",
     opensslTarget pkgDir $ base / "crypto" / "pkcs12" / "p12_p8e.c",
     opensslTarget pkgDir $ base / "crypto" / "pkcs12" / "p12_sbag.c",
     opensslTarget pkgDir $ base / "crypto" / "pkcs12" / "p12_utl.c",
     opensslTarget pkgDir $ base / "crypto" / "poly1305" / "poly1305.c",
     opensslTarget pkgDir $ base / "crypto" / "poly1305" / "poly1305_ameth.c",
     opensslTarget pkgDir $ base / "crypto" / "poly1305" / "poly1305_pmeth.c",
     opensslTarget pkgDir $ base / "crypto" / "poly1305" / "poly1305-x86_64.s",
     opensslTarget pkgDir (base / "crypto" / "rand" / "drbg_ctr.c") #[modesPath],
     opensslTarget pkgDir $ base / "crypto" / "rand" / "drbg_lib.c",
     opensslTarget pkgDir $ base / "crypto" / "rand" / "rand_lib.c",
     opensslTarget pkgDir $ base / "crypto" / "rand" / "rand_unix.c",
     opensslTarget pkgDir $ base / "crypto" / "ripemd" / "rmd_dgst.c",
     opensslTarget pkgDir $ base / "crypto" / "sha" / "keccak1600-x86_64.s",
     opensslTarget pkgDir $ base / "crypto" / "sha" / "sha1dgst.c",
     opensslTarget pkgDir $ base / "crypto" / "sha" / "sha1-mb-x86_64.s",
     opensslTarget pkgDir $ base / "crypto" / "sha" / "sha1-x86_64.s",
     opensslTarget pkgDir $ base / "crypto" / "sha" / "sha256.c",
     opensslTarget pkgDir $ base / "crypto" / "sha" / "sha256-x86_64.s",
     opensslTarget pkgDir $ base / "crypto" / "sha" / "sha256-mb-x86_64.s",
     opensslTarget pkgDir $ base / "crypto" / "sha" / "sha512.c",
     opensslTarget pkgDir $ base / "crypto" / "sha" / "sha512-x86_64.s",
     opensslTarget pkgDir $ base / "crypto" / "stack" / "stack.c",
     opensslTarget pkgDir $ base / "crypto" / "store" / "loader_file.c",
     opensslTarget pkgDir $ base / "crypto" / "store" / "store_init.c",
     opensslTarget pkgDir $ base / "crypto" / "store" / "store_lib.c",
     opensslTarget pkgDir $ base / "crypto" / "store" / "store_register.c",
     opensslTarget pkgDir $ base / "crypto" / "ts" / "ts_lib.c",
     opensslTarget pkgDir $ base / "crypto" / "ui" / "ui_lib.c",
     opensslTarget pkgDir $ base / "crypto" / "ui" / "ui_null.c",
     opensslTarget pkgDir $ base / "crypto" / "ui" / "ui_openssl.c",
     opensslTarget pkgDir $ base / "crypto" / "x509" / "x_all.c",
     opensslTarget pkgDir $ base / "crypto" / "x509" / "x_attrib.c",
     opensslTarget pkgDir $ base / "crypto" / "x509" / "x_crl.c",
     opensslTarget pkgDir $ base / "crypto" / "x509" / "x_exten.c",
     opensslTarget pkgDir $ base / "crypto" / "x509" / "x_name.c",
     opensslTarget pkgDir $ base / "crypto" / "x509" / "x_pubkey.c",
     opensslTarget pkgDir $ base / "crypto" / "x509" / "x_req.c",
     opensslTarget pkgDir $ base / "crypto" / "x509" / "x_x509.c",
     opensslTarget pkgDir $ base / "crypto" / "x509" / "x_x509a.c",
     opensslTarget pkgDir $ base / "crypto" / "x509" / "x509_att.c",
     opensslTarget pkgDir $ base / "crypto" / "x509" / "x509_cmp.c",
     opensslTarget pkgDir $ base / "crypto" / "x509" / "x509_def.c",
     opensslTarget pkgDir $ base / "crypto" / "x509" / "x509_ext.c",
     opensslTarget pkgDir $ base / "crypto" / "x509" / "x509_lu.c",
     opensslTarget pkgDir $ base / "crypto" / "x509" / "x509_obj.c",
     opensslTarget pkgDir $ base / "crypto" / "x509" / "x509_req.c",
     opensslTarget pkgDir $ base / "crypto" / "x509" / "x509_set.c",
     opensslTarget pkgDir $ base / "crypto" / "x509" / "x509_trs.c",
     opensslTarget pkgDir $ base / "crypto" / "x509" / "x509_v3.c",
     opensslTarget pkgDir $ base / "crypto" / "x509" / "x509_vfy.c",
     opensslTarget pkgDir $ base / "crypto" / "x509" / "x509_vpm.c",
     opensslTarget pkgDir $ base / "crypto" / "x509" / "x509cset.c",
     opensslTarget pkgDir $ base / "crypto" / "x509" / "x509name.c",
     opensslTarget pkgDir $ base / "crypto" / "x509" / "x509rset.c",
     opensslTarget pkgDir $ base / "crypto" / "x509v3" / "pcy_cache.c",
     opensslTarget pkgDir $ base / "crypto" / "x509v3" / "pcy_data.c",
     opensslTarget pkgDir $ base / "crypto" / "x509v3" / "pcy_lib.c",
     opensslTarget pkgDir $ base / "crypto" / "x509v3" / "pcy_map.c",
     opensslTarget pkgDir $ base / "crypto" / "x509v3" / "pcy_node.c",
     opensslTarget pkgDir $ base / "crypto" / "x509v3" / "pcy_tree.c",
     opensslTarget pkgDir $ base / "crypto" / "x509v3" / "v3_addr.c",
     opensslTarget pkgDir $ base / "crypto" / "x509v3" / "v3_admis.c",
     opensslTarget pkgDir $ base / "crypto" / "x509v3" / "v3_akey.c",
     opensslTarget pkgDir $ base / "crypto" / "x509v3" / "v3_akeya.c",
     opensslTarget pkgDir $ base / "crypto" / "x509v3" / "v3_alt.c",
     opensslTarget pkgDir $ base / "crypto" / "x509v3" / "v3_asid.c",
     opensslTarget pkgDir $ base / "crypto" / "x509v3" / "v3_bcons.c",
     opensslTarget pkgDir $ base / "crypto" / "x509v3" / "v3_bitst.c",
     opensslTarget pkgDir $ base / "crypto" / "x509v3" / "v3_conf.c",
     opensslTarget pkgDir $ base / "crypto" / "x509v3" / "v3_cpols.c",
     opensslTarget pkgDir $ base / "crypto" / "x509v3" / "v3_crld.c",
     opensslTarget pkgDir $ base / "crypto" / "x509v3" / "v3_enum.c",
     opensslTarget pkgDir $ base / "crypto" / "x509v3" / "v3_extku.c",
     opensslTarget pkgDir $ base / "crypto" / "x509v3" / "v3_genn.c",
     opensslTarget pkgDir $ base / "crypto" / "x509v3" / "v3_ia5.c",
     opensslTarget pkgDir $ base / "crypto" / "x509v3" / "v3_info.c",
     opensslTarget pkgDir $ base / "crypto" / "x509v3" / "v3_int.c",
     opensslTarget pkgDir $ base / "crypto" / "x509v3" / "v3_lib.c",
     opensslTarget pkgDir $ base / "crypto" / "x509v3" / "v3_ncons.c",
     opensslTarget pkgDir  (base / "crypto" / "x509v3" / "v3_ocsp.c") #[ocspPath],
     opensslTarget pkgDir $ base / "crypto" / "x509v3" / "v3_pci.c",
     opensslTarget pkgDir $ base / "crypto" / "x509v3" / "v3_pcia.c",
     opensslTarget pkgDir $ base / "crypto" / "x509v3" / "v3_pcons.c",
     opensslTarget pkgDir $ base / "crypto" / "x509v3" / "v3_pku.c",
     opensslTarget pkgDir $ base / "crypto" / "x509v3" / "v3_pmaps.c",
     opensslTarget pkgDir $ base / "crypto" / "x509v3" / "v3_purp.c",
     opensslTarget pkgDir $ base / "crypto" / "x509v3" / "v3_skey.c",
     opensslTarget pkgDir $ base / "crypto" / "x509v3" / "v3_sxnet.c",
     opensslTarget pkgDir $ base / "crypto" / "x509v3" / "v3_tlsf.c",
     opensslTarget pkgDir $ base / "crypto" / "x509v3" / "v3_utl.c"
   ]

extern_lib libcrypto :=
  let libFile := __dir__ / buildDir / cDir / "libcrypto.a"
  let dependencies := opensslTargets __dir__
  staticLibTarget libFile dependencies

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"@"867d773bc4f006475ccc7168ab478fb909bc792c"

package crypto {
  -- customize layout
  srcDir := "lib"
  libRoots := #[`Crypto]
  moreLeancArgs := #["-O3"]
}

lean_lib Crypto {
  moreLinkArgs := #["-Xlinker", "--error-limit=0"]
  -- moreLinkArgs := #["-L", (pkgDir / "deps" / "openssl-1.1.1l").toString, "-lcrypto"]
}

@[defaultTarget]
lean_exe crypto {
  root := `Main
  moreLinkArgs := #["-Xlinker", "--error-limit=0"]
  -- moreLinkArgs := #["-L", (pkgDir / "deps" / "openssl-1.1.1l").toString, "-lcrypto"]
}