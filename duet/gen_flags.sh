#!/bin/sh

OS="$1"

case "$OS" in
    macosx)
        echo '(-cclib -Wl,-keep_dwarf_unwind)';;
    *)
        ;;
esac
