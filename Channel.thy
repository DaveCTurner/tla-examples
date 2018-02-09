theory Channel
  imports "TLA-Utils"
begin

record 'Data chan =
  val :: 'Data
  rdy :: bool
  ack :: bool

locale Channel =
  fixes chan :: "'Data chan stfun"
  assumes chan_basevars: "basevars chan"

context Channel
begin

definition init where
  "init \<equiv> PRED rdy<chan> = ack<chan>"

definition Send where
  "Send d \<equiv> ACT (rdy<$chan> = ack<$chan> \<and> chan$ = (\<lambda>c. c \<lparr> val := d, rdy := \<not>rdy c\<rparr>)<$chan>)"

definition Rcv where
  "Rcv \<equiv> ACT (rdy<$chan> \<noteq> ack<$chan> \<and> chan$ = (\<lambda>c. c \<lparr> ack := \<not>ack c\<rparr>)<$chan>)"

definition Spec where
  "Spec \<equiv> TEMP Init init \<and> \<box>[(\<exists>d. Send d) \<or> Rcv]_chan"

end

definition AppendVal :: "'Data list \<Rightarrow> 'Data chan \<Rightarrow> 'Data list" where "AppendVal q c = q @ [val c]"

locale InnerFIFO
  = ichan: Channel ichan
  + ochan: Channel ochan
  for   ichan :: "'Data chan stfun"
    and ochan :: "'Data chan stfun"
    +
  fixes q :: "'Data list stfun"
  assumes ioq_basevars: "basevars (ichan, ochan, q)"

context InnerFIFO
begin

definition init where "init \<equiv> PRED (ichan.init \<and> ochan.init \<and> q = #[])"

definition SSend where "SSend d \<equiv> ACT (ichan.Send d \<and> unchanged(ochan,q))"
definition RRcv where "RRcv \<equiv> ACT (ochan.Rcv \<and> unchanged (ichan,q))"
definition BufRcv where "BufRcv \<equiv> ACT (ichan.Rcv \<and> q$ = AppendVal<$q, $ichan> \<and> unchanged ochan)"
definition BufSend where "BufSend \<equiv> ACT
  ($q \<noteq> #[]
  \<and> (\<exists>d. hd<$q> = #d \<and> ochan.Send d)
  \<and> q$ = tl<$q>
  \<and> unchanged ichan)"

definition Next where "Next \<equiv> ACT ((\<exists> msg. SSend msg) \<or> BufRcv \<or> BufSend \<or> RRcv)"
definition Spec where "Spec \<equiv> TEMP Init init \<and> \<box>[Next]_(ichan, ochan, q)"

end

locale FIFO
  = ichan: Channel ichan
  + ochan: Channel ochan
  for   ichan :: "'Data chan stfun"
    and ochan :: "'Data chan stfun"
    +
  assumes io_basevars: "basevars (ichan, ochan)"

context FIFO
begin

definition Spec :: temporal where "Spec \<equiv> TEMP (\<exists>\<exists>q. InnerFIFO.Spec ichan ochan q)"