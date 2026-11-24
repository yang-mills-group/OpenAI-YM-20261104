import YM.XSpace.Velour
/-!
# Adjacent budgets at lower fields and at the explicit counterterm through this triangle

Use either presence-at-root on harmonic scenarios or pay finite fixed lower labels.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Relief
open Function Set Filter Lattice Trace Chart2 Maxwell Maxwell.Free Photo Cirrus Foundation Chiral Graph3 Stall Playpen Future Drama Mu JetGauge Pages Next.Rank.Normal MvPolynomial Finsupp Asymptotics Normalize Structure1
open scoped Topology BigOperators InnerProductSpace Classical
variable {G:Gauge}(W:Initialize G)(g:G.Simple)(c:Shade.Cut) {ι:Type}{L: Filter ι}{a:ι→ℝ}{x y z:ι→Cover}{u v:E4}
variable (s: Relief.Stage L a)(hu:distance L a (fun i=> x i-z i) u) (hv:distance L a (fun i=> y i-z i) v)(hUV:u ≠ v)
include hu hv s in
lemma coreTickets [L.IsCountablyGenerated] (ha:5*c.rOut≤ ‖u‖)(hb:5*c.rOut≤ ‖v‖):
    SimplePay W g (fun i=> Chapter.compCost c W (Bfield G) (a i)) z x y L a:=by
  let P i (_:Unit):= Chapter.compCost c W (Bfield G) (a i); let T: Club G ι:= Stall.interior s.zero s.good c 6
  have H:Admits (together L) T P:= Stall.relief W (Bfield G) c s.zero s.good T rfl
  have he(w:ι→Cover)(u:E4)(h:distance L a w u)(e:5*c.rOut≤‖u‖)(p:Name G): (fun i=> bake (cameU W g (a i) (w i) p))∈T:=by
    let x(_ : Unit):= w; let f:= uTicket W g p; have ht: Poses L a x (fun _=>u) {()}:=⟨fun _ _=>h, fun (_: Unit) _ _ _ _=>Subsingleton.elim ..⟩
    exact (factor s.zero s.good _ 6 ht (fun _ _=> e)).births () (Finset.mem_singleton_self ()) f (wakesL g (W.surveys 4) false p)
  exact ⟨H.2 0 T.zero_mem,fun i j=> (admit_steps (together L) T (admit_steps (together L) T H (he _ v hv hb j)) (he _ u hu ha i)).2 0 T.zero_mem⟩
include hu hv s hUV in
theorem unpaid [L.IsCountablyGenerated] (ha:5*c.rOut≤ ‖u‖)(hb:5*c.rOut≤ ‖v‖): Tendsto (fun i=> base (a i)^14 * bottom W g (x i) (y i) (tribute W c (a i) (z i))) L (𝓝 0) :=
 (lowest W g s hu hv hUV (coreTickets W g c s hu hv ha hb)).congr (fun i=>by unfold tribute Chapter.compCost; rw [map_smul,map_smul]; simp only [base,smul_eq_mul,← mul_assoc, ← pow_add ])

variable {d:ℕ}
lemma records_peek {P:ι→ Stamp G}(h:Records a L x P):Likely L fun i=> peek G (P i):=by
  induction h with
  | unit => simp only [Pi.one_apply,map_one]; exact Likely.const ..
  | zero => simp only [Pi.zero_apply,map_zero]; exact Likely.zero
  | scale h c hp H=> unfold Stall.chain; simp_rw [map_smul]; exact hp.smul H
  | add x y H W=> simp_rw [Pi.add_apply,map_add]; exact H.add W
  | receive f s p IH=> simp only [Pi.mul_apply,map_mul,pencil, peek_leg,zero_mul]; exact Likely.zero
include hu hv s in
lemma pays_records {P:ι→ Stamp G}(h: Records a L (fun _=>0) P)(h1:u≠0)(h2:v≠0): SimplePay W g P z x y L a:=by
  have he {P:ι→Stamp G}(H:Records a L (fun _=>0) P)(u:E4)(t:ι→Cover)(ht: distance L a t u)(hv:u≠0)(p: Name G): Records a L (fun _=>0) (fun i=> Ξ (cameU W g (a i) (t i) p) (P i)):= by
    apply Records.biting (x:=fun _=>0) H; intro f _; exact position_pay (uTicket W g p) f ht (show distance L a (fun _=>0) 0 by unfold distance Playpen.actual; simp_rw [show Further.FreeCovariance.KP.rcast 0=0 by ext i; simp [Further.FreeCovariance.KP.rcast]]; simp [tendsto_const_nhds]) hv s.zero s.good
  refine ⟨records_peek h,fun i j=> records_peek (he (he h v _ hv h2 j) u _ hu h1 i)⟩
-- arbitrary base-mark member of rank criterion
variable (p:Sec G d)
def openP (a:ℝ): Stamp G:=∑ i:Fin (d+1),base a^i.val • Prelude.enter0 (W.surveys i) (Normalize.part _ i p)
lemma open_loc (z:Cover)(a:ℝ): μ0 W d a z p=freeze (Trace.volume z (openP W p a)):=by unfold openP μ0 assemble; simp_rw [LinearMap.sum_apply,LinearMap.comp_apply,map_sum,base_ice0,snaps,map_smul];rfl
lemma opening : Records a L (fun _=>0) (fun i=> openP W p (a i)):=by
  let b (k:Fin (d+1)): HP G k.val:= Normalize.part _ k p; let T k i:= reading (fun _=>0) a (Prelude.enter0 (W.surveys (k:Fin (d+1)).val) (b k)) k.val i; have he (k):Records a L (fun _=>0) (T k):= Records.program _ _ (status (W.surveys k.val) (b k))
  have hh (f:Finset (Fin (d+1))):Records a L (fun _=>0) (fun i=>∑ j∈f,T j i):=by induction f using Finset.induction_on with | empty=> simp only [Finset.sum_empty]; exact Records.zero| insert i f h ih=> simp_rw [Finset.sum_insert h]; exact Records.add (he i) ih
  have ht(v:Stamp G):Trace.volume 0 v=v:= same (fun A=>by rw [ting,show zone 0 A=A from funext fun i=>by simp [zone_ap]])
  specialize hh Finset.univ; simp_rw [T,Stall.reading,ht] at hh; exact hh
lemma openPV (z:Cover)(a:ℝ): Trace.volume z (openP W p a)∈ DegZ (UnitIndex G) (d/2):=by
  apply name_charge _ _ -- notation
  unfold openP; apply Submodule.sum_mem; intro i _; apply Submodule.smul_mem; have he := P0_cap W (en (show i.val≤d from Nat.lt_succ_iff.mp i.isLt) (Normalize.part d i p)); rw [Bracket.solo,Bracket.premiere] at he; exact he
end YM.XSpace.Relief
