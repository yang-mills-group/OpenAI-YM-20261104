import YM.SchemeConversionRG11.FirstW.Fold.Net
import YM.Pert.Scale.Bank
/-! Three-same stamps and correlations with near pair legs, exact including actual offsets. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW.Deck
open Function MeasureTheory Filter Set Lattice Pert Align Position Maxwell RawLabels MvPolynomial Warp SchemeConversionRG11
open scoped BigOperators Classical
variable {G:Gauge}{F:Labels.Frames G}{n:Side}{r d k:ℕ} (p:Players G r 6)(s:Fin r)(o:Full.Grid n r)(h:ℝ)(A:Sky G (Per n))
abbrev act (o:Full.Grid n r)(x:At G r d):= o x.1
def stagedV (p:Players G r 6) (o:Full.Grid n r)(h:ℝ)(a b c:At G r 6) (T:Sky G (Per n)):= ↑(T (arise h o a) (arise h o b) (arise h o c))*ZeroR o h (dict c (dict b (dict a p)))
def group3 (p:Players G r 6)(o:Full.Grid n r)(h:ℝ)(s:Fin r) := ∑ a:Who G 6,∑ b:Who G 6,∑ c:Who G 6, (verbD o h p (s,a) (s,b) (s,c) +changeD o h p (s,a) (s,b) (s,c))
def group2 (p:Players G r 6)(o:Full.Grid n r)(h:ℝ)(s:Fin r)(T:Sky G (Per n)) := ∑ a:Who G 6,∑ b:Who G 6,∑ i∈apart G 6 s, (3*stagedV p o h (s,a) (s,b) i T+ 2*changeD o h p (s,a) (s,b) i)
-- homogeneous rank3 part always
lemma head_cap (k : E F 6) (q:p s=cloak F k)(a b c:Who G 6) : ZeroR o h (dict (s,c) (dict (s,b) (dict (s,a) p))) = root3 (p s) a b c * ZeroR o h (air p s) := by
 obtain ⟨L,H⟩:=pays_slot p s o h; simp only [dict,update_self,update_idem,q,air] -- bill can't implicit? 
 rw [←H,←H,show pderiv c _ =_ from bill_three F k a b c]; rw [show C (σ:=Who G 6) (root3 _ _ _ _)=root3 (cloak F k) a b c • (1:Part G 6) from by simp [smul_eq_C_mul], map_smul, smul_eq_mul]
lemma turnV (A B C:FullT G n)(x: Site n): lapSky G n (tracing x A) (tracing x B) (tracing x C)=lapSky G n A B C := by simp only [lap_shield,wheels,tower_translate]; exact Equiv.sum_comp (Equiv.addRight x) (fun i=> ∑ t:Ticket,∑ s:Ticket,tower G i (icon (fresh t) (fresh s)) A B C)
lemma cap_reads (k:E F 6) (q:p s=cloak F k): group3 p o h s= currency F n h k * ZeroR o h (air p s) := by
 let X(a:Who G 6):= torT n 6 h (o s) a
 have hT(a:Who G 6): torT n 6 h 0 a=tracing (o s) (X a) := by simp [X,torT,river,consumes]
 unfold currency moon group3; simp only [LinearMap.coe_mk,AddHom.coe_mk,Finset.sum_mul]; apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; apply Finset.sum_congr rfl; intro c _; rw [hT,hT,hT,turnV]; simp only [verbD,changeD, head_cap p s o h k q, q,echoLeg, LinearMap.smul_apply, echo_translate,zero_add]
 simp only [Complex.ofReal_add, smul_eq_mul]; unfold X torT arise; simp only; ring
lemma dict_pair (a b:Who G 6): dict (s,b) (dict (s,a) p)= update p s (D1 b (D1 a (p s))) := by simp [dict]
lemma ally (i:At G r 6)(e:i∈apart G 6 s): air (dict i p) s=dict i (air p s) := (dict_b p s i e _).symm
lemma middle (k:E F 6)(q:p s = cloak F k)(a b:Who G 6)(i:At G r 6)(he:i∈apart G 6 s):
    ZeroR o h (dict i (dict (s,b) (dict (s,a) p)))= loot (cloak F k) a b * ZeroR o h (dict i (air p s)) + ∑ l:Who G 6, root3 (cloak F k) a b l* (∑ j∈apart G 6 s, ↑(dues o h (s,l) j)*ZeroR o h (dict j (dict i (air p s)))) := by
  rw [dict_pair,dict_b p s i he,q,bill_two F]
  obtain ⟨L,H⟩:= pays_slot (dict i p) s o h
  rw [← H,L.map_add,_root_.map_sum]; apply congrArg₂ (·+·)
  · rw [show C _ = loot (cloak F k) a b • (1:Part G 6) from by simp [MvPolynomial.smul_eq_C_mul], map_smul,H]; exact congrArg _ (congrArg (ZeroR o h) (ally p s i he))
  exact Finset.sum_congr rfl fun l _=>by rw [C_mul',map_smul,H,gives_one,ally p s i he];rfl
def glist (k:E F 6)(o:Full.Grid n r)(h:ℝ)(T:Sky G (Per n)) (u: At G r 6→At G r 6→ℝ)(s:Fin r)(i j:At G r 6):= ∑ a:Who G 6,∑ b:Who G 6,∑ c:Who G 6, root3 (cloak F k) a b c * (↑(sectorA (torT n 6 h (o s)) h (o s) T a b (arise h o i) * u (s,c) j):ℂ)
def trestle (k:E F 6)(o:Full.Grid n r)(h:ℝ)(T:Sky G (Per n))(u: At G r 6→At G r 6→ℝ)(s:Fin r)(p:Players G r 6):= ∑ i∈apart G 6 s,∑ j∈apart G 6 s, glist k o h T u s i j*ZeroR o h (dict j (dict i (air p s)))
lemma net_print (k:E F 6)(q:p s=cloak F k)(hg:G.Simple)(A:Sky G (Per n))(hv:∀ u: G.El,∀ a b c,A (putting u a) (putting u b) (putting u c)=A a b c): group2 p o h s A = trestle k o h A (dues o h) s p := by
  let R:= apart G 6 s
  unfold group2; conv_lhs=> arg 2; intro a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i hi
  let P a b:=sectorA (torT n 6 h (o s)) h (o s) A a b (arise h o i)
  let M(c:Who G 6):= ∑ j∈apart G 6 s, ↑(dues o h (s,c) j)*ZeroR o h (dict j (dict i (air p s)))
  let f:= ZeroR o h (dict i (air p s))
  have he a b: 3*stagedV p o h (s,a) (s,b) i A+2*changeD o h p (s,a) (s,b) i=(↑(P a b):ℂ)*(loot (cloak F k) a b * f + ∑ c,root3 (cloak F k) a b c*M c) := by
     unfold stagedV changeD; rw [middle p s o h k q a b i hi]; unfold P torT sectorA f M arise; simp only [Complex.ofReal_add,LinearMap.add_apply, LinearMap.smul_apply,smul_eq_mul,Complex.ofReal_mul, Complex.ofReal_ofNat]; ring
  have hP (a b): ↑(P a b)*(loot (cloak F k) a b*f)=(loot (cloak F k) a b * (↑(P a b):ℂ))*f:=by ring
  have hp: ∑ a:Who G 6,∑ b:Who G 6, loot (cloak F k) a b*(↑(P a b):ℂ)=0:= one_open F k (o s) h hg (arise h o i) A hv -- signature zinc
  simp_rw [he,mul_add,Finset.sum_add_distrib,hP,← Finset.sum_mul]; rw [hp,zero_mul,zero_add];
  have gt(a b:Who G 6): ↑(P a b) * (∑ c:Who G 6, root3 (cloak F k) a b c * M c) = ∑ j∈apart G 6 s,∑ c:Who G 6, root3 (cloak F k) a b c * ↑(P a b*dues o h (s,c) j)* ZeroR o h (dict j (dict i (air p s))) := by
    unfold M; simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro u _; apply Finset.sum_congr rfl; intro v _; simp only [Complex.ofReal_mul];ring
  simp_rw [gt]; conv_lhs=>arg 2; intro b; rw [Finset.sum_comm]
  rw [Finset.sum_comm]; simp only [glist,Finset.sum_mul];rfl
end YM.RG11.FirstW.Deck
