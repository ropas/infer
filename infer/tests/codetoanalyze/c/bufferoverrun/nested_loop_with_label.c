void nested_loop_with_label(){
  int i, j = 0;
  char a[10];

  for(i = 0; i < 10; i++){
  outer_loop:
    a[j] = 'a';			/* BUG */
    for(j = 0; j <= 10; j++){
      if(j >= 10) goto outer_loop;
    }
  }
}
