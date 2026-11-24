import YM.WilsonCoeffUV.Vacuum.UV.RatioLimit
/-!
# UV limits over all finer cuts with inherited aperture

Logical constants and spot estimates adaptive. Limit symbols on true cover
for entire ℕ-sequence of finer UV top N, NOT obtained by reading the actual
interacting beta trajectory. Calendar choice independent of horizon/read,
using sector admissions. totalized where a point may have no limit (no
claims on it).
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Next.Free Extension.UV.Linear PathCost Realm PowerSeries
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{n N M e m i k r b j l:ℕ}{U V W T:Credit}{ξ:Type*}

open Classical in
def coming {V:Type*} [Zero V][TopologicalSpace V](F:ℕ →  V):V:= if h: ∃ v,Tendsto F atTop (𝓝 v) then h.choose else 0
variable {δ:ℕ → ℝ}{s a:ℝ}
section
variable {V:Type*} [NormedAddCommGroup V][CompleteSpace V]
lemma augC {F:ℕ →  V}(h:Tendsto δ atTop (𝓝 0))(p: ∀ᶠ b:ℕ in atTop,∀ i j, b ≤ i →  b ≤  j →  ‖F i-F j‖ ≤  δ b) : Tendsto F atTop (𝓝 (coming F)) := by
   have he: CauchySeq F:= by
       rw [Metric.cauchySeq_iff]; intro ε hk
       obtain ⟨b,hb,w⟩:= (p.and (h.eventually_lt_const hk)).exists
       exact ⟨b,fun i hi j hj=> by rw [dist_eq_norm]; exact (hb i j hi hj).trans_lt w⟩
   unfold coming; rw [dif_pos (cauchySeq_tendsto_of_complete he)]; exact (cauchySeq_tendsto_of_complete he).choose_spec
variable {P:ℕ →  Ten V (Cloth ξ) r}
abbrev oblige (F:ℕ →  Ten V (Cloth ξ) r): Ten V (Cloth ξ) r:= fun x=> coming fun i=>F i x
lemma spirit (h:Tendsto δ atTop (𝓝 0))(hp:∀ b≥m, ∀ N M, b ≤ N → b ≤  M →  PairA s a (δ b) (P N) (P M))(x:Fin r → Cloth ξ): Tendsto (fun N=>P N x) atTop (𝓝 (oblige P x)):= by
    let y (b:ℕ):= a*δ b * Real.exp (-s*soar terrain x)
    have hy : Tendsto y atTop (𝓝 0):= by simpa only [zero_mul,mul_zero] using (h.const_mul a).mul_const (Real.exp (-s*soar terrain x))
    apply augC hy; exact (eventually_ge_atTop m).mono (fun b hb i j hi hj=> (hp b hb i j hi hj).visit.2 x)
lemma wane (h:Tendsto δ atTop (𝓝 0))(hp:∀ b≥m, ∀ N M, b ≤ N → b ≤  M →  PairA s a (δ b) (P N) (P M))(e:m ≤ b)(v:b ≤ N): PairA s a (δ b) (P N) (oblige P):= by
    refine ⟨(hp b e N N v v).pose,⟨(hp b e N N v v).nn,fun x=> le_of_tendsto (spirit h hp x).norm ?_⟩,⟨(hp b e N N v v).visit.1,fun x=> le_of_tendsto (tendsto_const_nhds.sub (spirit h hp x)).norm ?_⟩⟩
    · exact (eventually_ge_atTop b).mono fun n hn=> (hp b e n n hn hn).pose.2 x
    exact (eventually_ge_atTop b).mono fun n hn=> (hp b e N n v hn).visit.2 x
end
-- some matrices
def rackV {α β:Type*}(F:ℕ → ropes Cover α β): ropes Cover α β:= of fun i j=>coming (fun n=>F n i j)
lemma troops {α β:Type*} {F:ℕ → ropes Cover α β}(h:Tendsto δ atTop (𝓝 0))(p:∀ b≥ m,∀ i j,b ≤  i →  b ≤  j →  Ballast s a (δ b) (F i) (F j))(i j): Tendsto (fun n=>F n i j) atTop (𝓝 (rackV F i j)):=by
   let y (b:ℕ):= a * δ b * Real.exp (-s*terrain.gap i.1 j.1)
   have he: Tendsto y atTop (𝓝 0):=by simpa only [zero_mul,mul_zero] using (h.const_mul a).mul_const (Real.exp (-s*terrain.gap i.1 j.1))
   apply augC he; exact (eventually_ge_atTop m).mono (fun b v i' j' hi hj=> (p b v i' j' hi hj).between.2 i j)
lemma vaulted {α β:Type*}{F: ℕ → ropes Cover α β}(h:Tendsto δ atTop (𝓝 0))(p:∀ b≥ m,∀ i j,b ≤  i →  b ≤  j →  Ballast s a (δ b) (F i) (F j))(he:m ≤ b)(v:b ≤ N): Ballast s a (δ b) (F N) (rackV F):=by
    refine ⟨(p b he N N v v).oneP,⟨(p b he N N v v).nn,fun i j=> le_of_tendsto (troops h p i j).abs ?_⟩,⟨(p b he N N v v).between.1,fun i j=> le_of_tendsto (tendsto_const_nhds.sub (troops h p i j)).abs ?_⟩⟩
    · exact (eventually_ge_atTop b).mono fun N hv=> (p b he N N hv hv).oneP.2 i j
    exact (eventually_ge_atTop b).mono fun M hv=> (p b he N M v hv).between.2 i j

variable (A:Levels G)(Ñ:ChartRatio G)
abbrev rightF (A:Levels G)(m N:ℕ):= plain G (freeForms A N m)
abbrev middleF (A:Levels G)(m N:ℕ):= shuttleM (feedA A N m)
abbrev leftF (A:Levels G)(m N:ℕ):= shuttleM (conditional A N m)
abbrev holdZ (A: Levels G)(m:ℕ) := rackV (rightF A m)
abbrev holdΓ (A:Levels G)(m:ℕ):=rackV (leftF A m)
abbrev holdM (A:Levels G)(m:ℕ):=rackV (middleF A m)
def timeless (m : ℕ): Canvas G := fun j r=> oblige (fun i=>actionW A Ñ i m j r)
-- bona fide constitution of independent step law from timeless, not by taking subsequence independently

def eternal (m:ℕ): Canvas G:= tinge (loose A m) A.clock.kernel Ñ (holdZ A m) (holdΓ A m) (holdM A m) (timeless A Ñ (m+1))
def viridian (m:ℕ): Cost:= Kstar (eternal A Ñ m)
variable {A Ñ}
lemma inherited (p:Traces G e U V i j)(R:Realm G e U)(h:R.anchor ≤ m) (q:m ≤ b)(v:b ≤ N): PairA (R.mint m h).σ (R.cash V m) (R.tempC m b) (actionW R.draws R.paid N m i j) (timeless R.draws R.paid m i j) := wane (P:=fun N=>actionW R.draws R.paid N m i j) (PathCost.fade R.draws.S m) (fun b hb N M hn hm=>p R _ _ b N M hb hn hm) q v
lemma timeless_pt (p:i ≤ e)(R:Realm G e U) (h:R.anchor ≤ m) (r) (x:Fin r → YForest G): Tendsto (fun N=> actionW R.draws R.paid N m i r x) atTop (𝓝 (timeless R.draws R.paid m i r x)):=by
   obtain ⟨V,H⟩:= full_vacuum G e U
   exact spirit (PathCost.fade R.draws.S m) (P:=fun N=> actionW R.draws R.paid N m i r) (fun b hb N M hn hm=> H i p r R _ h b N M hb hn hm) x
lemma peg (R:Realm G e U) (h:R.anchor ≤ m)(q:m ≤ b)(v:b ≤ N): Ballast (R.mint m h).s (R.mint m h).D (R.cash (dome U) m * R.tempC m b) (rightF R.draws m N) (holdZ R.draws m):=by
   let θ:= fun b=>R.cash (dome U) m*R.tempC m b
   have he: Tendsto θ atTop (𝓝 0):=by simpa only [zero_mul,mul_zero] using (PathCost.fade R.draws.S m).const_mul (R.cash (dome U) m)
   exact vaulted (F:=rightF R.draws m) he (fun i j N M p t=> ((R.mint m h).cardG.kite i N M j p t).partial (R.won h j)) q v
lemma stride_pegs (R: Realm G e U)(h:R.anchor ≤ m)(q:m<b)(v:b ≤ N): Ballast (R.mint m h).s (R.mint m h).D (R.cash (doubling U) m * R.tempC m b) (middleF R.draws m N) (holdM R.draws m) ∧ Ballast (R.mint m h).s (R.mint m h).D (R.cash (doubling U) m * R.tempC m b) (leftF R.draws m N) (holdΓ R.draws m):=by
   let θ:= fun b=>R.cash (doubling U) m*R.tempC m b
   have he: Tendsto θ atTop (𝓝 0):=by simpa only [zero_mul,mul_zero] using (PathCost.fade R.draws.S m).const_mul (R.cash (doubling U) m)
   refine ⟨vaulted (F:=middleF R.draws m) he (fun i (p:m+1 ≤ i) N M t z=> ((R.mint m h).cardG.shift _ _ _ p t z).1.partial (R.dominates_both h p).2) q v,
       vaulted (F:=leftF R.draws m) he (fun i (p:m+1 ≤  i) N M t z=> ((R.mint m h).cardG.shift _ _ _ p t z).2.partial (R.dominates_both h p).2) q v⟩
end YM.WilsonCoeffUV.Bank
