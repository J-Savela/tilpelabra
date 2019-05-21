open util/ordering[Timestep]
//open util/integer

/* TODO:
  * Add channel failure scenarios
    - package dropping
    - package reordering
    (- package duplication?)
    (- package corruption?)
  * Which properties to check?
    - data arrive in correct order
    - no duplication of data
    - no missing data
    (- deadlock?)
    (- livelock?)
*/

// Signatures for states
abstract sig SenderState { seqNum: SequenceNumber }
sig ReadyToSend extends SenderState {}
sig WaitingForAck extends SenderState {}

abstract sig ReceiverState { seqNum: SequenceNumber }
sig WaitingForPacket extends ReceiverState {}


// Signatures for seqnums and packets
abstract sig SequenceNumber {nextNum: SequenceNumber}
one sig Seq_0 extends SequenceNumber {}{nextNum = Seq_1}
one sig Seq_1 extends SequenceNumber {}{nextNum = Seq_0}

sig Data {}
abstract sig Packet {
  seqNum: SequenceNumber
}
sig DataPacket extends Packet {
  payload: Data
}
sig AckPacket extends Packet {}

// Signatures for single timestep
sig Timestep {
  buffer_in: seq Data,
  sent: lone Data,
  acked: seq Data,
  buffer_out: seq Data,
  state_s: SenderState,
  state_r: ReceiverState,
  channel_s_to_r: seq DataPacket,
  channel_r_to_s: seq AckPacket
}

pred init [t: Timestep] {
  t.state_s in ReadyToSend
  t.state_s.seqNum = Seq_0
  t.state_r in WaitingForPacket
  t.state_r.seqNum = Seq_0
  //t.buffer_in.isEmpty
  #t.sent = 0
  t.acked.isEmpty
  t.buffer_out.isEmpty
  t.channel_s_to_r.isEmpty
  t.channel_r_to_s.isEmpty
}

pred sender_send [t_pre, t_post: Timestep] {
	// Keep this stuff the same
  //t_pre.buffer_in = t_post.buffer_in
  //t_pre.sent = t_post.sent
  t_pre.acked = t_post.acked
  t_pre.buffer_out = t_post.buffer_out
  //t_pre.state_s = t_post.state_s
  t_pre.state_s.seqNum = t_post.state_s.seqNum
  t_pre.state_r = t_post.state_r
  t_pre.state_r.seqNum = t_post.state_r.seqNum
  //t_pre.channel_s_to_r = t_post.channel_s_to_r
  t_pre.channel_r_to_s = t_post.channel_r_to_s

  // Precondition
  t_pre.state_s in ReadyToSend
  not t_pre.buffer_in.isEmpty
  
  // Postcondition
  t_post.state_s in WaitingForAck
  t_post.state_s.seqNum = t_pre.state_s.seqNum
  t_post.buffer_in = t_pre.buffer_in.rest
  t_post.sent = t_pre.buffer_in.first
  some p: DataPacket {
    t_post.channel_s_to_r = t_pre.channel_s_to_r.add [p]
    p.payload = t_pre.buffer_in.first
    p.seqNum = t_pre.state_s.seqNum
  }
}

pred sender_timeout [t_pre, t_post: Timestep] {
	// Keep this stuff the same
  t_pre.buffer_in = t_post.buffer_in
  t_pre.sent = t_post.sent
  t_pre.acked = t_post.acked
  t_pre.buffer_out = t_post.buffer_out
  t_pre.state_s = t_post.state_s
  t_pre.state_s.seqNum = t_post.state_s.seqNum
  t_pre.state_r = t_post.state_r
  t_pre.state_r.seqNum = t_post.state_r.seqNum
  //t_pre.channel_s_to_r = t_post.channel_s_to_r
  t_pre.channel_r_to_s = t_post.channel_r_to_s

  // Precondition
  t_pre.state_s in WaitingForAck
  
  // Postcondition
  some p: DataPacket {
    t_post.channel_s_to_r = t_pre.channel_s_to_r.add [p]
    p.payload = t_pre.buffer_in.first
    p.seqNum = t_pre.state_s.seqNum
  }
}

pred sender_rcvAck [t_pre, t_post: Timestep] {
	// Keep this stuff the same
  t_pre.buffer_in = t_post.buffer_in
  //t_pre.sent = t_post.sent
  //t_pre.acked = t_post.acked
  t_pre.buffer_out = t_post.buffer_out
  //t_pre.state_s = t_post.state_s
  //t_pre.state_s.seqNum = t_post.state_s.seqNum
  t_pre.state_r = t_post.state_r
  t_pre.state_r.seqNum = t_post.state_r.seqNum
  t_pre.channel_s_to_r = t_post.channel_s_to_r
  //t_pre.channel_r_to_s = t_post.channel_r_to_s

  // Precondition
  not t_pre.channel_r_to_s.isEmpty
  
  // Postcondition
  t_post.channel_r_to_s = t_pre.channel_r_to_s.rest
  t_pre.state_s in ReadyToSend implies {
    t_pre.sent = t_post.sent
    t_pre.acked = t_post.acked
    t_pre.state_s = t_post.state_s
    t_pre.state_s.seqNum = t_post.state_s.seqNum
  }
  t_pre.state_s in WaitingForAck implies {
    t_pre.channel_r_to_s.first.seqNum = t_pre.state_s.seqNum implies {
        #t_post.sent = 0
        t_post.acked = t_pre.acked.add[t_pre.sent]
        t_post.state_s in ReadyToSend
        t_post.state_s.seqNum = t_pre.state_s.seqNum.nextNum
      }
    t_pre.channel_r_to_s.first.seqNum != t_pre.state_s.seqNum implies {
        t_pre.sent = t_post.sent
        t_pre.acked = t_post.acked
        t_pre.state_s = t_post.state_s
        t_pre.state_s.seqNum = t_post.state_s.seqNum
      }
  }
}

pred receiver_rcvPacket [t_pre, t_post: Timestep] {
	// Keep this stuff the same
  t_pre.buffer_in = t_post.buffer_in
  t_pre.sent = t_post.sent
  t_pre.acked = t_post.acked
  //t_pre.buffer_out = t_post.buffer_out
  t_pre.state_s = t_post.state_s
  t_pre.state_s.seqNum = t_post.state_s.seqNum
  //t_pre.state_r = t_post.state_r
  //t_pre.state_r.seqNum = t_post.state_r.seqNum
  //t_pre.channel_s_to_r = t_post.channel_s_to_r
  //t_pre.channel_r_to_s = t_post.channel_r_to_s

  // Precondition
  not t_pre.channel_s_to_r.isEmpty
  
  // Postcondition
  some p: DataPacket {
    p = t_pre.channel_s_to_r.first
    t_post.channel_s_to_r = t_pre.channel_s_to_r.rest
    t_pre.state_r.seqNum = p.seqNum implies {
      some q: AckPacket {
        t_post.channel_r_to_s = t_pre.channel_r_to_s.add[q]
        q.seqNum = p.seqNum
      }
      t_post.buffer_out = t_pre.buffer_out.add[p.payload]
      t_post.state_r.seqNum = t_pre.state_r.seqNum.nextNum
    }
    t_pre.state_r.seqNum != p.seqNum implies {
      some q: AckPacket {
        t_post.channel_r_to_s = t_pre.channel_r_to_s.add[q]
        q.seqNum = t_pre.state_r.seqNum.nextNum
      }
      t_post.buffer_out = t_pre.buffer_out
      t_post.state_r.seqNum = t_pre.state_r.seqNum
    }
  }
}

pred channel_dropData [t_pre, t_post: Timestep] {
	// Keep this stuff the same
  t_pre.buffer_in = t_post.buffer_in
  t_pre.sent = t_post.sent
  t_pre.acked = t_post.acked
  t_pre.buffer_out = t_post.buffer_out
  t_pre.state_s = t_post.state_s
  t_pre.state_s.seqNum = t_post.state_s.seqNum
  t_pre.state_r = t_post.state_r
  t_pre.state_r.seqNum = t_post.state_r.seqNum
  //t_pre.channel_s_to_r = t_post.channel_s_to_r
  t_pre.channel_r_to_s = t_post.channel_r_to_s

  // Precondition
  not t_pre.channel_s_to_r.isEmpty
  
  // Postcondition
  some i: Int {
    lt[i, #t_pre.channel_s_to_r]
    lte[0, i]
    t_post.channel_s_to_r = t_pre.channel_s_to_r.delete[i]
  }
}

pred channel_dropAck [t_pre, t_post: Timestep] {
	// Keep this stuff the same
  t_pre.buffer_in = t_post.buffer_in
  t_pre.sent = t_post.sent
  t_pre.acked = t_post.acked
  t_pre.buffer_out = t_post.buffer_out
  t_pre.state_s = t_post.state_s
  t_pre.state_s.seqNum = t_post.state_s.seqNum
  t_pre.state_r = t_post.state_r
  t_pre.state_r.seqNum = t_post.state_r.seqNum
  t_pre.channel_s_to_r = t_post.channel_s_to_r
  //t_pre.channel_r_to_s = t_post.channel_r_to_s

  // Precondition
  not t_pre.channel_r_to_s.isEmpty
  
  // Postcondition
  some i: Int {
    lt[i, #t_pre.channel_r_to_s]
    lte[0, i]
    t_post.channel_r_to_s = t_pre.channel_r_to_s.delete[i]
  }
}

pred channel_reorderData [t_pre, t_post: Timestep] {
	// Keep this stuff the same
  t_pre.buffer_in = t_post.buffer_in
  t_pre.sent = t_post.sent
  t_pre.acked = t_post.acked
  t_pre.buffer_out = t_post.buffer_out
  t_pre.state_s = t_post.state_s
  t_pre.state_s.seqNum = t_post.state_s.seqNum
  t_pre.state_r = t_post.state_r
  t_pre.state_r.seqNum = t_post.state_r.seqNum
  //t_pre.channel_s_to_r = t_post.channel_s_to_r
  t_pre.channel_r_to_s = t_post.channel_r_to_s

  // Precondition
  #t_pre.channel_s_to_r > 1
  
  // Postcondition
  some i, j: Int {
    lt[i, #t_pre.channel_s_to_r]
    lte[0, i]
    lt[j, #t_pre.channel_s_to_r]
    lte[0, j]
    i != j
    let oldPacket_i = t_pre.channel_s_to_r[i] |
    let oldPacket_j = t_pre.channel_s_to_r[j] {
      oldPacket_i != oldPacket_j
      t_post.channel_s_to_r = t_pre.channel_s_to_r.setAt[i, oldPacket_j].setAt[j, oldPacket_i]
    }
  }
}

pred channel_reorderAck [t_pre, t_post: Timestep] {
	// Keep this stuff the same
  t_pre.buffer_in = t_post.buffer_in
  t_pre.sent = t_post.sent
  t_pre.acked = t_post.acked
  t_pre.buffer_out = t_post.buffer_out
  t_pre.state_s = t_post.state_s
  t_pre.state_s.seqNum = t_post.state_s.seqNum
  t_pre.state_r = t_post.state_r
  t_pre.state_r.seqNum = t_post.state_r.seqNum
  t_pre.channel_s_to_r = t_post.channel_s_to_r
  //t_pre.channel_r_to_s = t_post.channel_r_to_s

  // Precondition
  #t_pre.channel_r_to_s > 1
  
  // Postcondition
  some i, j: Int {
    lt[i, #t_pre.channel_r_to_s]
    lte[0, i]
    lt[j, #t_pre.channel_r_to_s]
    lte[0, j]
    i != j
    let oldPacket_i = t_pre.channel_r_to_s[i] |
    let oldPacket_j = t_pre.channel_r_to_s[j] {
      oldPacket_i != oldPacket_j
      t_post.channel_r_to_s = t_pre.channel_r_to_s.setAt[i, oldPacket_j].setAt[j, oldPacket_i]
    }
  }
}


/*
The traces fact constrains the timesteps to follow only the allowed transitions.
The first formulation of data arriving eventually fails if the channel doesn't move
anything and the sender keeps timing out. Without timeouts, no counterexample is found.
*/
/*
fact traces_reliable_channel {
  init[first]
  all t0: Timestep - last |
  let t1 = t0.next | 
  sender_send[t0, t1] or
  sender_timeout[t0, t1] or
  sender_rcvAck[t0, t1] or
  receiver_rcvPacket[t0, t1]
}
*/
assert data_arrives_eventually_v1 {
  all t0: Timestep |
  some d: Data | 
  d in t0.buffer_in.elems implies some t1: Timestep - t0 | d in t1.buffer_out.elems
}

check data_arrives_eventually_v1 for 5

/*
Data arriving eventually could possibly be formulated in terms of the sender not
progressing to the next state before the data has arrived and has been acked. 
*/

assert data_arrives_eventually_v2 {
  all t: Timestep |
  t.state_s = ReadyToSend implies
  #t.acked = #t.buffer_out
}

check data_arrives_eventually_v2 for 1










pred show {
  some t0, t1, t2, t3: Timestep {
    t0 = first
    t1 = t0.next
    t2  =t1.next
    t3  =t2.next
    init[t0]
    sender_send[t0,t1]
    receiver_rcvPacket[t1,t2]
    sender_rcvAck[t2,t3]
  }
}
pred show2 {
  #ReceiverState > 1
}

run show for 15 but 4 Timestep
