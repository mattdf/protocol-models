module protocols/hop2

open util/ordering[Block] as TO
open util/ordering[Value] as VO

/* --------Signature sets and relations ----------- */
/* ------------------------------------------------ */

sig Block {}

sig Value {}

sig Address {}

sig Transfer {
	recipient: one Address,
}

sig Messenger {
	L1Bridge: one Address,
	L2Bridge: one Address
}

one sig Bonder extends Address {}

abstract sig BalanceState {
	credit: Address -> Value -> Block,
	debit: Address -> Value -> Block,
}

abstract sig BridgeState extends BalanceState {
	committedRoots: TransferRoot -> Block,
	bondedTransfers: Address -> Transfer -> Block,
	spentTransfers: Transfer -> Block
}

one sig Chain extends BridgeState {
	bondedRoots: TransferRoot -> Block,
	rollups: set Rollup
}

some sig Rollup extends BridgeState {
	chain: one Chain,
	messenger: one Messenger,
	pendingTransfers: Transfer -> Block,
	HBalance: Address -> Value -> Block
} {
	Bonder not in messenger.L1Bridge + messenger.L2Bridge
	messenger.L1Bridge != messenger.L2Bridge
}

sig TransferRoot {
	leaves: set Transfer
}

/* ---- Utility functions for complex mappings ---- */
/* ------------------------------------------------ */

fun getDebit(c: BalanceState, a: Address, t: Block): set Value {
	c.debit.t [a]
}

fun getCredit(c: BalanceState, a: Address, t: Block): set Value {
	c.credit.t [a]
}

fun getHBalance(c: Rollup, a: Address, t: Block): set Value {
	c.HBalance.t [a]
}

fun insolvent(b: BalanceState, a: Address, t: Block): set Value {
	 getDebit[b, a, t] & (getCredit[b, a, t] + getCredit[b, a, t].nexts)
}

fun allPreviouslyBondedTransfers(c: Chain, a: Address, t: Block): set Transfer {
	c.bondedTransfers.(t.prevs) [a]
}

fun allPreviouslyBondedRoots(c: Chain, t: Block): set TransferRoot {
	c.bondedRoots.(t.prevs)
}

fun allPreviouslyCommittedRoots(b: BridgeState, t: Block): set TransferRoot {
	b.committedRoots.(t.prevs)
}

/* ---------- Universal Environment Facts --------- */
/* ------------------------------------------------ */

fact RootHash {
	all t: TransferRoot | #t.leaves > 1
}

fact NoRootOverlap {
	no disj r, r': TransferRoot | some r.leaves & r'.leaves
}

fact DistinctBridges {
	no disj m, m': Messenger | m.L1Bridge = m'.L1Bridge or m.L2Bridge = m'.L2Bridge
	#Rollup = #Messenger
}

fact AddressBalances {
	all a: Address, t: Block, c: BalanceState | #(c.credit.t [a]) = 1 and #(c.debit.t [a]) = 1
}

/* ----------- Initial Trace States --------------- */
/* ------------------------------------------------ */

pred init [t: Block] {
	all a: Address, b: BalanceState {
		getCredit[b, a, t] = VO/first
		getDebit[b, a, t] = VO/first
	}

	all b: BridgeState, a: Address {
		b.committedRoots.t = none
		b.bondedTransfers.t [a] = none
		b.spentTransfers.t = none
	}

	all c: Chain {
		c.bondedRoots.t = none
		c.rollups = Rollup
	}

	all r: Rollup, a: Address {
		r.chain = Chain
		r.pendingTransfers.t = none
		getHBalance[r, a, t] = VO/first
	}

}

/* ----------------- Main trace ------------------- */
/* ------------------------------------------------ */

fact traces {
	init [first]
	all t: Block-last |
		let t' = t.next |
			all l2: Rollup | all a: Address | some r: TransferRoot, tr: Transfer {
				L2Actions[a, l2, r, tr, t, t']
			}

	all t: Block-last |
		let t' = t.next |
			all a: Address | some r: TransferRoot, tr: Transfer {
				L1Actions[a, r, tr, t, t']
			}


	all t: Block-last |
		let t' = t.next | all l2: Rollup | some r: TransferRoot, tr: Transfer {
				(no a: Address | sendToL1[a, l2, tr, t, t'] or commitTransfers[a, l2, Chain, r, t, t']) implies l2.pendingTransfers.t' = l2.pendingTransfers.t
				(no a: Address | L2BridgeActions[a, l2, r, t, t']) implies l2.committedRoots.t' = l2.committedRoots.t
				(no a: Address | L1BridgeActions[a, Chain, r, t, t']) implies Chain.committedRoots.t' = Chain.committedRoots.t
				some a, recipient: Address, t: Block-last | sendToL2[a, Chain, l2, recipient, t, t.next]
		}

	all t: Block-last |
		let t' = t.next | all l2: Rollup | some tr: Transfer {
				withdrawL1[Chain, tr, t, t'] or (some a: Address | bondWithrawalL1[a, Chain, tr, t, t']) or Chain.spentTransfers.t' = Chain.spentTransfers.t
				withdrawL2[l2, tr, t, t'] or (some a: Address | bondWithrawalL2[a, l2, tr, t, t'] or bondWithdrawalAndDistribute[a, l2, tr, t, t']) or l2.spentTransfers.t' = l2.spentTransfers.t
		}

}

/* -- L1 disjoint action set for a time interval -- */
/* ------------------------------------------------ */

pred L1Actions[a: Address, r: TransferRoot, tr: Transfer, t, t': Block] {
	L1AddressMapActions[a, Chain, tr, t, t']
	L1BonderActions[a, Chain, r, t, t']
	L1BridgeActions[a, Chain, r, t, t']
}


pred L1AddressMapActions[a: Address, l1: Chain, tr: Transfer, t, t': Block] {
	skipL1AddressMap[a, Chain, t, t']
	or stakeL1[a, Chain, t, t']
	or unstakeL1[a, Chain, t, t']
	or bondWithrawalL1[a, Chain, tr, t, t']
}

pred L1BonderActions[a: Address, l1: Chain, r: TransferRoot, t, t': Block] {
	bondTransferRoot[a, Chain, r, t, t']
	or a in Bonder and l1.bondedRoots.t' = l1.bondedRoots.t
	or a not in Bonder
}

pred L1BridgeActions[a: Address, l1: Chain, r: TransferRoot, t, t': Block] {
	confirmTransferRoot[a, Chain, r, t, t'] and (some l2: Rollup, a2: Address | commitTransfers[a2, l2, Chain, r, t, t'])
	or skipL1Bridge[a, Chain, t, t']
	or a not in ((l1.rollups).messenger).L2Bridge
}


//* -- L2 disjoint action set for a time interval -- */
/* ------------------------------------------------ */

pred L2Actions[a: Address, l2: Rollup, r: TransferRoot, tr: Transfer, t, t': Block] {
	(L2AddressMapActions[a, l2, tr, t, t'] and L2BridgeActions[a, l2, r, t, t']) or (
		(
		sendToL1[a, l2, tr, t, t']
		or commitTransfers[a, l2, Chain, r, t, t']
		or bondWithrawalL2[a, l2, tr, t, t']
		) and (
		withdrawL2[l2, tr, t, t']
		or bondWithdrawalAndDistribute[a, l2, tr, t, t']
		)
	)
	//and (L2TransferActions[a, l2, tr, t, t'] or L2MessageActions[a, l2, r, t, t'] or some insolvent[l2, a, t])
}

pred L2AddressMapActions[a: Address, l2: Rollup, tr: Transfer, t, t': Block] {
	stakeL2[a, l2, t, t']
	or unstakeL2[a, l2, t, t']
	or skipL2[a, l2, t, t']
	or (mintHOPL2[a, l2, t, t'] and ((a = tr.recipient and tr in l2.spentTransfers.t') or (some a2: Address, tr2: Transfer | sendToL2[a2, Chain, l2, tr2.recipient, t, t'])))
	//or burnHOPL2[a, l2, t, t']
	or bondWithrawalL2[a, l2, tr, t, t']
	//or distribute[a, l2, Chain, tr, t, t']
}

pred L2BridgeActions[a: Address, l2: Rollup, r: TransferRoot, t, t': Block] {
	setTransferRoot[a, l2, r, t, t'] and (some a2: Address | confirmTransferRoot[a2, Chain, r, t, t'])
	or a in l2.messenger.L1Bridge and l2.committedRoots.t' = l2.committedRoots.t
	or a not in l2.messenger.L1Bridge
}

pred L2TransferActions[a: Address, l2: Rollup, tr: Transfer, t, t': Block] {
	sendToL1[a, l2, tr, t, t']
}

pred L2MessageActions[a: Address, l2: Rollup, r: TransferRoot, t, t': Block] {
	commitTransfers[a, l2, Chain, r, t, t']
}

/* -------------- L1 Trace Actions ---------------- */
/* ------------------------------------------------ */

pred skipL1AddressMap[a: Address, l1: Chain, t, t': Block] {
	getCredit[l1, a, t'] = getCredit[l1, a, t]
	getDebit[l1, a, t'] = getDebit[l1, a, t]
	l1.bondedTransfers.t' [a] = l1.bondedTransfers.t [a]
}

pred stakeL1 [a: Address, l1: Chain, t, t': Block] {
	a in Bonder
	getCredit[l1, a, t'] = getCredit[l1, a, t].next
	getDebit[l1, a, t'] = getDebit[l1, a, t]
	l1.bondedTransfers.t' [a] = l1.bondedTransfers.t [a]
}

pred unstakeL1 [a: Address, l1: Chain, t, t': Block] {
	no insolvent[l1, a, t]
	getCredit[l1, a, t'] = getCredit[l1, a, t]
	getDebit[l1, a, t'] = getDebit[l1, a, t].next
	l1.bondedTransfers.t' [a] = l1.bondedTransfers.t [a]
}

pred bondTransferRoot [a: Address, l1: Chain, r: TransferRoot, t, t': Block] {
	a in Bonder
	no insolvent[l1, a, t]
	r not in allPreviouslyBondedRoots[l1, t'] + allPreviouslyCommittedRoots[l1, t']
	getCredit[l1, a, t'] = getCredit[l1, a, t]
	getDebit[l1, a, t'] = getDebit[l1, a, t].next
	l1.bondedTransfers.t' [a] = l1.bondedTransfers.t [a]
	l1.bondedRoots.t' = l1.bondedRoots.t + r
}

pred confirmTransferRoot [a: Address, l1: Chain, r: TransferRoot, t, t': Block] {
	a in ((l1.rollups).messenger).L2Bridge
	r not in allPreviouslyCommittedRoots[l1, t']
	l1.bondedRoots.t' = l1.bondedRoots.t - r
	l1.committedRoots.t' = l1.committedRoots.t + r
}

pred bondWithrawalL1[a: Address, l1: Chain, tr: Transfer, t, t': Block] {
	a in Bonder
	tr not in l1.bondedTransfers.t [a]
	no insolvent[l1, a, t]
	getCredit[l1, a, t'] = getCredit[l1, a, t]
	getDebit[l1, a, t'] = getDebit[l1, a, t].next
	l1.bondedTransfers.t' [a] = l1.bondedTransfers.t [a] + tr
	l1.spentTransfers.t' = l1.spentTransfers.t + tr
}

pred skipL1Bridge[a: Address, l1: Chain, t, t': Block] {
	a in ((l1.rollups).messenger).L2Bridge
	//l1.bondedRoots.t' = l1.bondedRoots.t
	l1.committedRoots.t' = l1.committedRoots.t
}

pred sendToL2[a: Address, l1: Chain, l2: Rollup, recipient: Address, t, t': Block] {
	distribute[a, l2, Chain, recipient, t, t']
}

pred withdrawL1[l1: Chain, tr: Transfer, t, t': Block] {
	tr in (l1.committedRoots.t).leaves
	tr not in l1.spentTransfers.t
	l1.spentTransfers.t' = l1.spentTransfers.t + tr
}


/* -------------- L2 Trace Actions ---------------- */
/* ------------------------------------------------ */

pred skipL2[a: Address, l2: Rollup, t, t': Block] {
	getCredit[l2, a, t'] = getCredit[l2, a, t]
	getDebit[l2, a, t'] = getDebit[l2, a, t]
	getHBalance[l2, a, t'] = getHBalance[l2, a, t]
	l2.bondedTransfers.t' [a] = l2.bondedTransfers.t [a]
}

pred stakeL2 [a: Address, l2: Rollup, t, t': Block] {
	a in Bonder
	getCredit[l2, a, t'] = getCredit[l2, a, t].next
	getDebit[l2, a, t'] = getDebit[l2, a, t]
	getHBalance[l2, a, t'] = getHBalance[l2, a, t]
	l2.bondedTransfers.t' [a] = l2.bondedTransfers.t [a]
}

pred unstakeL2 [a: Address, l2: Rollup, t, t': Block] {
	no insolvent[l2, a, t]
	getCredit[l2, a, t'] = getCredit[l2, a, t]
	getDebit[l2, a, t'] = getDebit[l2, a, t].next
	getHBalance[l2, a, t'] = getHBalance[l2, a, t]
	l2.bondedTransfers.t' [a] = l2.bondedTransfers.t [a]
}

pred mintHOPL2 [a: Address, l2: Rollup, t, t': Block] {
	getCredit[l2, a, t'] = getCredit[l2, a, t]
	getDebit[l2, a, t'] = getDebit[l2, a, t]
	getHBalance[l2, a, t'] = getHBalance[l2, a, t].next
	l2.bondedTransfers.t' [a] = l2.bondedTransfers.t [a]
}

pred burnHOPL2 [a: Address, l2: Rollup, t, t': Block] {
	no VO/first & getHBalance[l2, a, t]
	getCredit[l2, a, t'] = getCredit[l2, a, t]
	getDebit[l2, a, t'] = getDebit[l2, a, t]
	getHBalance[l2, a, t'] = getHBalance[l2, a, t].prev
	l2.bondedTransfers.t' [a] = l2.bondedTransfers.t [a]
}

pred bondWithrawalL2[a: Address, l2: Rollup, tr: Transfer, t, t': Block] {
	a in Bonder
	tr not in l2.bondedTransfers.t [a]
	no insolvent[l2, a, t]
	getDebit[l2, a, t'] = getDebit[l2, a, t].next
	getCredit[l2, a, t'] = getCredit[l2, a, t]
	getHBalance[l2, a, t'] = getHBalance[l2, a, t]
	l2.bondedTransfers.t' [a] = l2.bondedTransfers.t [a] + tr
}

pred setTransferRoot[a: Address, l2: Rollup, r: TransferRoot, t, t': Block] {
	a in l2.messenger.L1Bridge
	r not in allPreviouslyCommittedRoots[l2, t']
	l2.committedRoots.t' = l2.committedRoots.t + r
}

pred sendToL1[a: Address, l2: Rollup, tr: Transfer, t, t': Block] {
	burnHOPL2[a, l2, t, t']
	tr not in l2.spentTransfers.t
	l2.pendingTransfers.t' = l2.pendingTransfers.t + tr
}

pred commitTransfers[a: Address, l2: Rollup, l1: Chain, r: TransferRoot, t, t': Block] {
	mintHOPL2[a, l2, t, t']
	#l2.pendingTransfers.t > 0
	l2.pendingTransfers.t' = none
	let transfers = l2.pendingTransfers.t {
		r.leaves in transfers
		r not in l2.committedRoots.t
 	}
	confirmTransferRoot[l2.messenger.L2Bridge, l2.chain, r, t, t']
}

pred distribute[a: Address, l2: Rollup, l1: Chain, recipient: Address, t, t': Block] {
	a in l2.messenger.L1Bridge
	mintHOPL2[recipient, l2, t, t']
}


pred bondWithdrawalAndDistribute[a: Address, l2: Rollup, tr: Transfer, t, t': Block] {
	bondWithrawalL2[a, l2, tr, t, t']
	l2.spentTransfers.t' = l2.spentTransfers.t + tr
	mintHOPL2[tr.recipient, l2, t, t']
}

pred withdrawL2[l2: Rollup, tr: Transfer, t, t': Block] {
	tr in (l2.committedRoots.t).leaves
	tr not in l2.spentTransfers.t
	l2.spentTransfers.t' = l2.spentTransfers.t + tr
	mintHOPL2[tr.recipient, l2, t, t']
}


/* ------- Assertions for model checking ---------- */
/* ------------------------------------------------ */

assert ProtocolAssertions {
	all a: Address, t: Block, b: BalanceState | no (getDebit[b, a, t] & getCredit[b, a, t].nexts)

}

pred show {
	#Rollup = 1
	#Address > 3
	#TransferRoot > 1
	#Transfer > 1
	#(Chain.bondedRoots.Block) > 0
	some a: Address | a not in Bonder
	some t: Transfer | t not in TransferRoot.leaves
	some b: Bonder | #(Chain.bondedTransfers.Block [b]) > 1 and #(Rollup.bondedTransfers.Block [b]) > 1
	some b: Bonder | #(getCredit[Chain, b, Block] - VO/first) > 0
	some b: Bonder | #(getDebit[Chain, b, Block] - VO/first) > 0
	some t: Block | #Chain.committedRoots.t > 0
	some t: Block | #Chain.spentTransfers.t > 0
	some t: Block | #Rollup.spentTransfers.t > 0
	all tr: Transfer | tr.recipient not in Messenger.L1Bridge + Messenger.L2Bridge + Bonder
	some t: Block, r: Rollup | #r.pendingTransfers.t > 0 and {
		some t': Block | t' in t.nexts and #r.pendingTransfers.t' = 0
	}
}

check ProtocolAssertions for 4 but 2 Rollup, 2 Messenger, 20 Block, 20 Value, 4 TransferRoot, 6 Transfer
//check NoRootOverlap for 7 Block, 6 Value, 5 TransferRoot, 1 Messenger, 6 Transfer, 1 Bonder, 1 Chain, 2 Rollup
// run show for 7 Block, 10 Value, 5 TransferRoot, 1 Messenger, 6 Transfer, 1 Bonder, 1 Chain, 2 Rollup, 5 Address
//run show for 7 but 1 Bonder, 2 Rollup, 8 Address, 15 Value, 2 Messenger
run show for 6 but 2 Rollup, 2 Messenger, 20 Block, 4 TransferRoot, 6 Transfer
//run show
