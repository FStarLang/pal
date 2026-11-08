module Pulse.Lib.C.Palow.ConstSeq

module L = FStar.List.Tot
module Seq = FStar.Seq

let const_seq xs = Seq.seq_of_list xs

let const_seq_len xs = ()

let const_seq_index xs i = FStar.Seq.Properties.lemma_seq_of_list_index xs i
