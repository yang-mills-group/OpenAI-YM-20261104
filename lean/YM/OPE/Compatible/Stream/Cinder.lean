import YM.OPE.Compatible.Stream.Lock
import YM.OPE.Compatible.Parcels.Lakes
/-! Actual operator convergence for shadow Train. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free.Frequency
open Function Filter Set Lattice Laurent Bloch Metric Exterior Matrix Precision RG Work.F08 OPE.Flume
open scoped Topology BigOperators ComplexConjugate
variable {L:Side} {i d j k:ℕ} {η x U a B:ℝ}
local notation "T"=> TypeFace 2
variable {C:KernelChoices}
abbrev Op (C:KernelChoices)(v:Train j):Row (TypeFace 1) (TypeFace 1):= composeRows (composeRows (transRows (cobound 1)) (pink C.penalty v)) (cobound 1)
abbrev helm (b:ℝ) := (Fintype.card T:ℝ)^2 * b^2
lemma catch_k {A:Row T T} (v w: Train j) (hr:Key C v w A) (hv:tow A η x) (hη:0<η)(hg:(cobound 1).strip η a) (hj:4 ≤ j): (Op C v - Op C w).strip η (helm a*x):=by
   let p := composeRows (composeRows (transRows (cobound 1)) A) (cobound 1)
   have hZ: p.strip η (helm a*x):=by apply strip_mono (strip_compose hη.le (strip_compose hη.le (strip_trans hg) hv.1) hg) le_rfl; apply le_of_eq; unfold helm; ring
   have hl :Whole p:=⟨η,_,hη,hZ⟩; let W:=Whole.boundary 1
   have hx(s:Row T T)(n:Side)(hh:Whole s): (composeRows (composeRows (transRows (cobound 1)) s) (cobound 1)).acts n=K (s.acts n):=by rw [(W.flipped.prod hh).acts W, W.flipped.acts hh,acts_trans];rfl
   let H(v:Train j):= (heart_saves C.penalty C.penalty_pos hj (fun x:Train j=>x)).1.whole v
   have hs(v:Train j): Whole (Op C v):=(W.flipped.prod (H v)).prod W
   have he : p=Op C v-Op C w:= bank_injective hl.safe ((hs v).minus (hs w)).safe fun n=> by
       rw [show _ = K (A.acts n) from hx A n ⟨η,_,hη,hv.1⟩,hr n]; symm; change (minusRows (Op C v) (Op C w)).acts n= _; rw [(hs v).less (hs w)]; unfold Op; rw [hx _ n (H v), hx _ n (H w)]
   rw [← he]; exact hZ
variable {Z:Patch}
lemma sameEnd {p : Train Z.J} (n m:ℕ): folder Z p (m+n)= folder Z (folder Z p m) n:=by induction n with
    | zero=>rfl
    | succ n ih=> change (ship Z (folder Z p (m+n))).land=(ship Z _).land; rw [ih]
structure Payer (C:KernelChoices)(Z:Patch)(η U a B:ℝ) :Prop where
    height : 0 < η
    pos : 0 ≤ B
    hugs : Covers η C.penalty U Z.J Z.J
    jets (i:Axis) : (pathJet T [i]).strip η a
    pinken (v:Train Z.J) : (pink C.penalty v).strip η B
    pole : ded η U a/(Z.L.val:ℝ)≤1/2
lemma sanction (h:Payer C Z η U a B) : ∃ v:ℝ,∀ (p q:Train Z.J)(i j:ℕ), i ≤ j→ ((Op C (folder Z p i))-(Op C (folder Z q j))).strip η (v*(1/2:ℝ)^i) := by
   obtain ⟨D,-,hD⟩:= delta_budget 1 η; refine ⟨helm D*(2*B),fun p q i j hi=>?_⟩
   obtain ⟨j,rfl⟩:= Nat.exists_eq_add_of_le hi; rw [add_comm i j,sameEnd]
   let v:= folder Z q j
   obtain ⟨R,hR,hv⟩:= starting (C:=C) h.height Z.order_cut (h.pinken p) (h.pinken v) -- args
   obtain ⟨S,hS,hq⟩:= last_window h.height h.hugs h.jets (mul_nonneg (by norm_num) h.pos) hR h.pole hv i
   apply strip_mono (catch_k _ _ hq hS h.height hD Z.order_cut) le_rfl; exact le_of_eq (by ring)
lemma K_station (h:Payer C Z η U a B): ∃ A:Row (TypeFace 1) (TypeFace 1), Whole A∧ ∃ v:ℝ,∀ (p:Train Z.J)(i:ℕ),(Op C (folder Z p i)-A).strip η (v*(1/2:ℝ)^i):=by
    obtain ⟨b,hb⟩:= sanction h; let P(i):= Op C (folder Z (.top Z.J) i)
    have hz: Tendsto (fun i:ℕ=> b * (1/2:ℝ)^i) atTop (𝓝 0):=by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (r:=1/2) (by norm_num : (0:ℝ)≤ 1/2) (by norm_num)).const_mul b
    choose A hp ht using fun i j:TypeFace 1=> Sack.finalSeq (f:=fun n=> P n i j) (u:=envelopeW η) (fun n m H=> hb (.top _) (.top _) n m H i j) hz (by intro x; exact Real.one_le_exp (mul_nonneg h.height.le (by positivity)))
    have ha(p:Train Z.J)(i:ℕ): ((Op C (folder Z p i))-A).strip η (b*(1/2:ℝ)^i):=by
       intro x y; exact Sack.closes (u:=envelopeW η) (f:=fun j=> (Op C (folder Z p i) x y)-(P j x y)) ((eventually_ge_atTop i).mono (fun j hj=>hb p (.top _) i j hj x y)) tendsto_const_nhds (p:=(Op C (folder Z p i) x y)-(A x y)) (fun a=>(tendsto_const_nhds (x:= Op C (folder Z p i) x y a)).sub (hp _ _ a)) (fun i=> (Real.exp_pos _).le)
    refine ⟨A,?_,b,ha⟩
    let W:= Whole.boundary 1; have he:Whole (P 0):= (W.flipped.prod (show Whole _ from ⟨η,B,h.height,h.pinken (.top Z.J)⟩)).prod W
    have hy : Whole (P 0-A):= ⟨_,_,h.height,ha (.top _) 0⟩
    rw [show A= P 0-(P 0-A) by abel]; exact he.minus hy
end YM.Next.Free.Frequency
