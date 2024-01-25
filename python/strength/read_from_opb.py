import csv
import codecs
import os


path = "/home/orestis/school/starexec/BENCH/"


# categories = ['EMPLSCHED', 'KNAP', 'MAXSAT', 'MIPLIB', 'MULT', 'PB16dec', 'PB16opt', 'PROOFdec', 'PROOFopt', 'SAT']

# for category in categories:

#     BLOCKSIZE = 1048576 # or some other, desired size in bytes

#     files = os.listdir(path + category)

#     for file in files:
#         if file.endswith(".opb"):
#             sourceFileName = path + category + "/" + file
#             # targetFileName = path + category + "/" + file[:-4] + ".cnf"
#             targetFileName = sourceFileName[:-4] + "utf8.opb"
#             # print(sourceFileName)
#             # print(targetFileName)
    
#             with codecs.open(sourceFileName, "r", "latin-1") as sourceFile:
#                 with codecs.open(targetFileName, "w", "utf-8") as targetFile:
#                     while True:
#                         contents = sourceFile.read(BLOCKSIZE)
#                         print(contents)
#                         if not contents:
#                             break
#                         targetFile.write(contents)

file = path + "KNAP/knapPI_11_20_1000_1_-1428.opb"
targetFileName = file[:-4] + "utf8.opb"

BLOCKSIZE = 1048576 # or some other, desired size in bytes

with codecs.open(file, "r", "latin-1") as sourceFile:
    with codecs.open(targetFileName, "w", "utf-8") as targetFile:
        while True:
            contents = sourceFile.read(BLOCKSIZE)
            print(contents)
            if not contents:
                break
            try:
                decoded_contents = contents.encode("latin-1").decode("utf-8")
            except UnicodeDecodeError:
                decoded_contents = contents.decode("latin-1", errors="replace")
                decoded_contents = decoded_contents.encode("utf-8").decode("utf-8")

            # decoded_contents = contents.encode("latin-1").decode("utf-8")
            print(decoded_contents)
            targetFile.write(decoded_contents)


# print("hello-dsbfeobfdl,1234F;èx_&fdµùfps^µù".encode("latin-1"))

# with open(file, "rb") as file:
#     # Read the bytes from the file
#     file_bytes = file.read()
    
#     # Print the content of the file as bytes
#     print(file_bytes)
#     file_bytes = file_bytes.decode("base64")
#     print(file_bytes)