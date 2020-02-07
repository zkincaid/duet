AC_INIT([duet],[0.1.3])

AC_ARG_WITH(bddbddb,
	[  --with-bddbddb=<DIR>      Directory containing bddbddb],
	[BDDBDDB_DIR="$withval"],
	[BDDBDDB_DIR="$PWD/lib"])

AC_SUBST(BDDBDDB_DIR,$BDDBDDB_DIR)

# symlink arch appropriate libbuddy.so
AC_MSG_CHECKING(machine architecture)
if test `uname -m` = "x86_64"; then
   AC_MSG_RESULT(64 bit)
   ln -s lib/libbuddy.so.64 lib/libbuddy.so
else
   AC_MSG_RESULT(32 bit)
   ln -s lib/libbuddy.so.32 lib/libbuddy.so
fi

AC_OUTPUT(duet/config.ml)
