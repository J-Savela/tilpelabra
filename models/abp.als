open util/ordering[Timestep]

/* TODO:
  * Add channel failure scenarios
    - package dropping
    - package reordering
    - package duplication?
    - package corruption?
  * Which properties to check?
    - data arrive in correct order
    - no duplication of data
    - no missing data
*/

// Signatures for states
abstract sig SenderState { seqNum: SequenceNumber }
sig ReadyToSend extends SenderState {}
sig WaitingForAck extends SenderState {}

abstract sig ReceiverState { seqNum: SequenceNumber }
sig WaitingForPacket extends ReceiverState {}


// Signatures for seqnums and packets
abstract sig SequenceNumber {next: SequenceNumber}
one sig Seq_0 extends SequenceNumber {}{next = Seq_1}
one sig Seq_1 extends SequenceNumber {}{next = Seq_0}

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
  buffer_out: seq Data,
  state_s: SenderState,
  state_r: ReceiverState,
  channel_s_to_r: seq DataPacket,
  channel_r_to_s: seq AckPacket
}

pred init [t: Timestep] {
  t.state_s = ReadyToSend
  t.state_s.seqNum = Seq_0
  t.state_r = WaitingForPacket
  t.state_r.seqNum = Seq_0
  t.buffer_in.isEmpty
  t.buffer_out.isEmpty
  t.channel_s_to_r.isEmpty
  t.channel_r_to_s.isEmpty
}

pred sender_send [t_pre, t_post: Timestep] {
	// Keep this stuff the same
  t_pre.buffer_in = t_post.buffer_in
  t_pre.buffer_out = t_post.buffer_out
  //t_pre.state_s = t_post.state_s
  t_pre.state_s.seqNum = t_post.state_s.seqNum
  t_pre.state_r = t_post.state_r
  t_pre.state_r.seqNum = t_post.state_r.seqNum
  //t_pre.channel_s_to_r = t_post.channel_s_to_r
  t_pre.channel_r_to_s = t_post.channel_r_to_s

  // Precondition
  t_pre.state_s = ReadyToSend
  not t_pre.buffer_in.isEmpty
  
  // Postcondition
  t_post.state_s = WaitingForAck
  some p: DataPacket {
    t_post.channel_s_to_r = t_pre.channel_s_to_r.add [p]
    p.payload = t_pre.buffer_in.first
    p.seqNum = t_pre.state_s.seqNum
  }
}

pred sender_timeout [t_pre, t_post: Timestep] {
	// Keep this stuff the same
  t_pre.buffer_in = t_post.buffer_in
  t_pre.buffer_out = t_post.buffer_out
  t_pre.state_s = t_post.state_s
  t_pre.state_s.seqNum = t_post.state_s.seqNum
  t_pre.state_r = t_post.state_r
  t_pre.state_r.seqNum = t_post.state_r.seqNum
  //t_pre.channel_s_to_r = t_post.channel_s_to_r
  t_pre.channel_r_to_s = t_post.channel_r_to_s

  // Precondition
  t_pre.state_s = WaitingForAck
  
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
  t_pre.state_s = ReadyToSend implies {
    t_pre.state_s = t_post.state_s
    t_pre.state_s.seqNum = t_post.state_s.seqNum
  }
  t_pre.state_s = WaitingForAck implies {
    t_pre.channel_r_to_s.first.seqNum = t_pre.state_s.seqNum implies {
        t_post.state_s = ReadyToSend
        t_post.state_s.seqNum = t_pre.state_s.seqNum.next
      }
    t_pre.channel_r_to_s.first.seqNum != t_pre.state_s.seqNum implies {
        t_pre.state_s = t_post.state_s
        t_pre.state_s.seqNum = t_post.state_s.seqNum
      }
  }
}

pred receiver_rcvPacket [t_pre, t_post: Timestep] {
	// Keep this stuff the same
  t_pre.buffer_in = t_post.buffer_in
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
      t_post.channel_r_to_s = t_pre.channel_r_to_s
      t_post.buffer_out = t_pre.buffer_out.add[p.payload]
      t_post.state_r.seqNum = t_pre.state_r.seqNum.next
    }
    t_pre.state_r.seqNum != p.seqNum implies {
      some q: AckPacket {
        t_post.channel_r_to_s = t_pre.channel_r_to_s.add[q]
        q.seqNum = t_pre.state_r.seqNum.next
      }
      t_post.buffer_out = t_pre.buffer_out
      t_post.state_r.seqNum = t_pre.state_r.seqNum
    }
  }
}

pred show [t_pre, t_post: Timestep] {
  receiver_rcvPacket[t_pre,t_post]
  let p = t_pre.channel_s_to_r.first |
  p.seqNum = t_pre.state_r.seqNum
}

run show for 5 but 2 Timestep
