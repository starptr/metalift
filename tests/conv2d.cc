#include <iostream>
#include "list.h"

extern "C" List<List<int>> test(List<List<int>> mat) {
  int rows = listLength(mat);
  int cols = listLength(listGet(mat, 0)); // TODO: handle empty `mat`?
  List<List<int>> convolved = newList<List<int>>();
  for (int i = 0; i < rows - 1; i++) {
    List<int> row = newList<int>();
    for (int j = 0; j < cols - 1; j++) {
      row = listAppend(row,
          - listGet(listGet(mat, i), j) + listGet(listGet(mat, i), j+1)
          - listGet(listGet(mat, i+1), j) + listGet(listGet(mat, i+1),j+1));
    }
    convolved = listAppend(convolved, row);
  }
  return convolved;
}

int main(int argc, char** argv) {
  const int size = 10;
  List<List<int>> mat = newList<List<int>>();
  for (int i = 0; i < size; i++) {
    List<int> row = newList<int>();
    for (int j = 0; j < size; j++) {
      row = listAppend(row, i*10+j);
    }
    mat = listAppend(mat, row);
  }
  List<List<int>> o = test(mat);

  for (int i = 0; i < size - 1; i++) {
    for (int j = 0; j < size - 1; j++) {
      std::cout << o->contents[i]->contents[j] << ", ";
    }
    std::cout << std::endl;
  }
  return 0;
}
