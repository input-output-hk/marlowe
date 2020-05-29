self: super:
let
  pkgs = super;
  sources = import ./../sources.nix;

  pkgsForOldPolyML = import sources.pkgsForOldPolyML {};
  polymlPatched = pkgsForOldPolyML.polyml.overrideAttrs(args: pkgs.recurseIntoAttrs(rec {
    configureFlags = args.configureFlags ++ ["--enable-intinf-as-int"];
  }));

  pkgsForIsabelle = import sources.pkgsForIsabelle {};

  rpath = pkgsForIsabelle.stdenv.lib.makeLibraryPath [
    pkgsForIsabelle.glib 
    pkgsForIsabelle.zlib
  ] + ":${pkgsForIsabelle.stdenv.cc.cc.lib}/lib64";

  isabelle2018 = pkgsForIsabelle.isabelle.overrideAttrs(args: pkgs.recurseIntoAttrs(rec {
    installPhase = args.installPhase + ''
        sed -i 's/RunCall.clearMutableBit state;//g' $out/Isabelle2018/src/Pure/Concurrent/synchronized.ML        
        #patchShebangs $out
        #$out/bin/isabelle build -s -b HOL''; # cache HOL
    postPatch = ''
        patchShebangs .
        cat >contrib/polyml-*/etc/settings <<EOF
          ML_SYSTEM_64=true
          ML_SYSTEM=${polymlPatched.name}
          ML_PLATFORM=${pkgsForIsabelle.stdenv.system}
          ML_HOME=${polymlPatched}/bin
          ML_OPTIONS="--minheap 1000"
          POLYML_HOME="\$COMPONENT"
          ML_SOURCES="\$POLYML_HOME/src"
        EOF
        cat >contrib/jdk/etc/settings <<EOF
          ISABELLE_JAVA_PLATFORM=${pkgsForIsabelle.stdenv.system}
          ISABELLE_JDK_HOME=${if pkgs.stdenv.isDarwin then "$(/usr/libexec/java_home)" else pkgs.openjdk8}
        EOF
        echo ISABELLE_LINE_EDITOR=${pkgsForIsabelle.rlwrap}/bin/rlwrap >>etc/settings
        for comp in contrib/jdk contrib/polyml-*; do
          rm -rf $comp/x86*
        done
        '' + (if ! pkgsForIsabelle.stdenv.isLinux then "" else ''
        arch=${if pkgsForIsabelle.stdenv.hostPlatform.system == "x86_64-linux" then "x86_64-linux" else "x86-linux"}
        for f in contrib/*/$arch/{bash_process,epclextract,eprover,nunchaku,SPASS,z3}; do
          patchelf --set-interpreter $(cat ${pkgsForIsabelle.stdenv.cc}/nix-support/dynamic-linker) "$f" || true
          patchelf --set-rpath ${rpath} "$f" || true
        done
    '');
  }));
      

in {
  polyml = polymlPatched;
  isabelle = isabelle2018;
}
