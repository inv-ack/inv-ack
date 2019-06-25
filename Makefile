CC=COQC
.PHONY: all
all: prelims.vo repeater.vo increasing_expanding.vo  inverse.vo countdown.vo applications.vo inv_ack.vo bin_prelims.vo bin_repeater.vo bin_countdown.vo bin_applications.vo bin_inv_ack.vo

prelims.vo: prelims.v
	$(CC) prelims.v

repeater.vo: prelims.vo repeater.v
	$(CC) repeater.v

increasing_expanding.vo: repeater.vo increasing_expanding.v
	$(CC) increasing_expanding.v

inverse.vo: prelims.vo repeater.vo increasing_expanding.vo inverse.v
	$(CC) inverse.v

countdown.vo: prelims.vo repeater.vo increasing_expanding.vo inverse.vo countdown.v
	$(CC) countdown.v

applications.vo: prelims.vo repeater.vo increasing_expanding.vo inverse.vo countdown.vo  applications.v
	$(CC) applications.v
	
inv_ack.vo: prelims.vo repeater.vo increasing_expanding.vo inverse.vo countdown.vo  applications.vo inv_ack.v
	$(CC) inv_ack.v

bin_prelims.vo: prelims.vo bin_prelims.v
	$(CC) bin_prelims.v

bin_repeater.vo: repeater.vo bin_prelims.vo bin_repeater.v
	$(CC) bin_repeater.v

bin_countdown.vo: countdown.vo bin_prelims.vo bin_repeater.vo bin_countdown.v
	$(CC) bin_countdown.v

bin_inverse.vo: inverse.vo bin_prelims.vo bin_inverse.v
	$(CC) bin_inverse.v

bin_applications.vo: applications.vo bin_prelims.vo bin_inverse.vo bin_applications.v
	$(CC) bin_applications.v

bin_inv_ack.vo: inv_ack.vo bin_prelims.vo bin_repeater.vo bin_countdown.vo bin_inverse.vo bin_inv_ack.v
	$(CC) bin_inv_ack.v

.PHONY: test
test:
	ocamlc test_runtime_ocaml.ml -o test && ./test; 
	ocamlc bin_test_runtime_ocaml.ml -o test && ./test
	
	
.PHONY: clean
clean:
	rm -f *.cmo *.cmi test *.vo *.glob