#!/bin/sh

MODTIME=$(stat -f '%Sm' -t '%F-%R' dbmonad.tex)
DEST="$HOME/Dropbox/Devel/ahmm/Notes/Substoids"

cp -a dbmonad.tex "$DEST/dbmonad-$MODTIME".tex
cp -a dbmonad.pdf "$DEST/dbmonad-$MODTIME".pdf
