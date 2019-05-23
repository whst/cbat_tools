set -x

dummy_dir=../dummy


run () {
  bap $dummy_dir/hello_world.out --pass=wp \
    --wp-compare=true \
    --wp-file1=main_1.bpj \
    --wp-file2=main_2.bpj \
    --wp-function=process_message \
    --wp-check-calls=true
}

run
