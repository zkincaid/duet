path_to_CS=/bat0/turetsky/CSFE_JAVA_API
path_to_OCAML=/bat0/turetsky/.opam/4.02.1+PIC
path_to_Clp=/bat0/turetsky/Clp-1.16.10

echo "************* Linking libduet.so: *************"
cd _build/duet/src/
# Add -verbose to the ocamlfind command for debugging

ocamlc -g -I $path_to_OCAML/lib -I . -c ../../../duet/src/plugin_interface.ml

mv ../../../duet/src/plugin_interface.cmo plugin_interface.cmo
mv ../../../duet/src/plugin_interface.cmi plugin_interface.cmi


ocamlc -g -I $path_to_OCAML/lib -I . -c ../../../duet/src/plugin_impl.ml

mv ../../../duet/src/plugin_impl.cmo plugin_impl.cmo
mv ../../../duet/src/plugin_impl.cmi plugin_impl.cmi

cd ../../..

echo "****** Successful end of make_libduet.sh ******"
