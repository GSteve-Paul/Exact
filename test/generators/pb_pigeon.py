import sys

if len(sys.argv)!=3:
	print("Usage: python3 script.py nb_pigeons nb_holes")

nb_pigeons = int(sys.argv[1])
nb_holes = int(sys.argv[2])

print("*",nb_pigeons,"pigeons",nb_holes,"holes")
print("* #variable=",nb_pigeons*nb_holes,"#constraint=",nb_holes)

def get_var(p,h):
	return 1+p*nb_holes+h
	
print("min: ",end="")
for p in range(0,nb_pigeons):
	for h in range(0,nb_holes):
		print("-1 x",get_var(p,h),end=" ",sep="")
print(";\n")

# every pigeon has at least one hole:
#for p in range(0,nb_pigeons):
	#for h in range(0,nb_holes):
		#print("+1 x",get_var(p,h),end=" ",sep="")
	#print(">= 1 ;")
	
# every hole has at most one pigeon:
for h in range(0,nb_holes):
	for p in range(0,nb_pigeons):
		print("-1 x",get_var(p,h),end=" ",sep="")
	print("= -1 ;")
