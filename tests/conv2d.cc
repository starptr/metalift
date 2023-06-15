#include <iostream>
#include "list.h"
#include "matrix.h"

extern "C" nestedList<int> test(nestedList<int> mat) {
  int rows = nestedLength(mat);
  int cols = listLength(nestedGet(mat, 0)); // TODO: handle empty `mat`?
  nestedList<int> convolved = nestednewList<int>();
  for (int i = 0; i < rows - 1; i++) {
    List<int> row = newList<int>();
    for (int j = 0; j < cols - 1; j++) {
      row = listAppend(row,
          - listGet(nestedGet(mat, i), j) + listGet(nestedGet(mat, i), j+1)
          - listGet(nestedGet(mat, i+1), j) + listGet(nestedGet(mat, i+1),j+1));
    }
    convolved = nestedAppend(convolved, row);
  }
  return convolved;
}

//int main(int argc, char** argv) {
//  const int size = 10;
//  nestedList<int> mat = newnestedList<int>();
//  for (int i = 0; i < size; i++) {
//    List<int> row = newList<int>();
//    for (int j = 0; j < size; j++) {
//      row = listAppend(row, i*10+j);
//    }
//    mat = listAppend(mat, row);
//  }
//  nestedList<int> o = test(mat);
//
//  for (int i = 0; i < size - 1; i++) {
//    for (int j = 0; j < size - 1; j++) {
//      std::cout << o->contents[i]->contents[j] << ", ";
//    }
//    std::cout << std::endl;
//  }
//  return 0;
//}
