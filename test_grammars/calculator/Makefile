
#Default build
main: calculator_definition.thc


#Silver build
calculator.jar: Abstract.sv
	silver -I .. calculator


#Abella build
calculator_definition.thc: calculator_definition.thm
	abella calculator_definition.thm -c calculator_definition.thc -o calculator_definition.out


#Clean up
part-clean:
	rm *.out *~ build.xml

clean:
	rm *.out *~ build.xml *.thc calculator.jar

