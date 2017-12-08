// def factorial(x:Int):Int = {
//   if (x == 1) {
//     1
//   }
//   else {
//     factorial(x-1) * x
//   }
// };
// var x = factorial(5);
// x

def succ(x: Int) = x + 1;
def twice(x: Int) = x + x;
printChar(functionCompose[Int,Int,Int](succ, twice)(39).toChar);
printChar(functionCompose[Int,Int,Int](succ, succ)(73).toChar);
printChar(functionCompose[Int,Int,Int](twice, succ)(4).toChar)