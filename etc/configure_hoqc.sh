#!/usr/bin/env bash
# Generator for standalone hoq-config

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )/.." >/dev/null && pwd )"
CONFIG_FILE="$DIR/hoq-config"

cat << 'EOF' > "$CONFIG_FILE"
#!/usr/bin/env bash
prefix="/usr/local"
export COQC="$(command -v coqc 2>/dev/null || echo coqc)"
export COQCHK="$(command -v coqchk 2>/dev/null || echo coqchk)"
export COQDEP="$(command -v coqdep 2>/dev/null || echo coqdep)"
export COQDOC="$(command -v coqdoc 2>/dev/null || echo coqdoc)"
export COQIDE="$(command -v coqide 2>/dev/null || echo coqide)"
export COQTOP="$(command -v coqtop 2>/dev/null || echo coqtop)"

function readlink_f() {
    TARGET_FILE="$1"
    cd "$(dirname "$TARGET_FILE")"
    TARGET_FILE=`basename "$TARGET_FILE"`
    while [ -L "$TARGET_FILE" ]
    do
        TARGET_FILE=`readlink "$TARGET_FILE"`
        cd "$(dirname "$TARGET_FILE")"
        TARGET_FILE=`basename "$TARGET_FILE"`
    done
    PHYS_DIR=`pwd -P`
    RESULT="$PHYS_DIR/$TARGET_FILE"
    echo "$RESULT"
}

mydir="$(dirname "$(readlink_f "${BASH_SOURCE[0]}")")"
which cygpath 2>/dev/null >/dev/null && mydir="$(cygpath -m "$mydir")"

SYS_COQLIB="$("$COQTOP" -where 2>/dev/null | tr -d '\r')"

if test -d "$mydir/coq/theories" && test -f "$mydir/coq/theories/Init/Prelude.vo"
then
  export COQLIB="$mydir/coq"
  export HOTTLIB="$mydir/theories"
  export HOTTCONTRIB="$mydir/contrib"
elif test -n "$SYS_COQLIB" && test -d "$SYS_COQLIB"
then
  export COQLIB="$SYS_COQLIB"
  export HOTTLIB="$mydir/theories"
  export HOTTCONTRIB="$mydir/contrib"
else
  export COQLIB="/usr/local/share/hott/coq"
  export HOTTLIB="/usr/local/share/hott/theories"
  export HOTTCONTRIB="/usr/local/share/hott/contrib"
fi
EOF

chmod +x "$CONFIG_FILE"
echo "Generated $CONFIG_FILE successfully."
