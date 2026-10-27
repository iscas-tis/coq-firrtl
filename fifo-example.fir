; This is an example of a FIFO queue with a capacity of up to 16 elements.
; The queue is implemented using a ring buffer.
; Comments starting with "demonstrate" do not need to be included in the paper;
; they should instead be explained in the text accompanying the example.

; The top module's rst input is AsyncReset so that all data types
; appear somewhere in the circuit but actually I think the module FIFO
; would work best with a synchronous reset.

; An empty buffer does not transmit the item directly, so an item
; that is being written can be read at the earliest in the next cycle.
; But a full buffer can be read and written at the same time:
; the current buffer element at first = last is read, and at the end
; of the cycle it will be replaced by the newly added in_item.data.

circuit T

module T
	input clk : Clock
	input rst : AsyncReset
	...

	instance FF of FIFO
	FF.clk <= clk
	FF.rst <= rst ; demonstrate reset inference (over module boundaries)
	FF.in_item.data <= ... ; demonstrate that width inference works over module boundaries


module FIFO ; demonstrate (almost) all data types in the module interface
	input in_item : { flip ack : UInt<1>, data : SInt, enable : UInt<1> } ; demonstrate bundle type, flipped fields
	input clk : Clock
	input rst : Reset ; demonstrate abstract reset
	output out_item : { is_empty : UInt<1>, data : SInt, flip ack : UInt<1> }

	; demonstrate (almost) all component types (register, wire, node) in the module internals
	reg buffer : SInt[16], clk
	regreset first : UInt<4>, clk, rst, UInt(0)
	regreset last : UInt<4>, clk, rst, UInt(0)
	regreset full : UInt<1>, clk, rst, UInt<1>(0)

	wire new_last : UInt<4>
	connect new_last, last ; demonstrate last connect semantics
	wire new_first : UInt<4>
	connect new_first, first
	node eq_new_first_new_last = eq(new_first, new_last)

	; in_item.ack is 1 iff a new item is being added to the buffer in this cycle.
	connect in_item.ack, and(or(not(full), out_item.ack), in_item.enable)
	when in_item.ack: ; demonstrate that outputs can be read within the module (to avoid repeating a definition)
		connect buffer[last], in_item.data ; demonstrate width inference
		connect new_last, add(last, UInt(1)) ; demonstrate that it will not infer width(new_last) = width(last)+1...
		connect last, new_last
		connect full, eq_new_first_new_last

	connect out_item.is_empty, and(eq(first, last), not(full))
	when not(out_item.is_empty):
		connect out_item.data, buffer[first]
		when out_item.ack:
			connect new_first, add(first, UInt(1))
			connect first, new_first ; demonstrate that it's not a combinatorial cycle, because first is a register
			connect full, and(full, eq_new_first_new_last) ; demonstrate last connect semantics
		else:
			skip ; demonstrate the need of skip to make the next else belong to the outer when statement
	else:
		invalidate out_item.data ; demonstrate that out_item.data must be connected always (it's not a register)

