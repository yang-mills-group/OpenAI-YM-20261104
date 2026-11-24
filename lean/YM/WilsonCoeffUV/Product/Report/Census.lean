import YM.WilsonCoeffUV.Product.Report.Layout
/-!
# Count root delivery costs
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Soil
open Gauge Power PathCost Precision Embroider Fountain Cosmos Shard Realm
open PowerSeries
open scoped Topology BigOperators
variable {n c:Side}{U V α β:Type*}{r h00 D j e i l k:ℕ}{A B C s:ℝ}{G:Gauge}
open Embroider
open scoped ContDiff
abbrev locale (o:CellR)(X: Era G Lounge): Era G ℝ:= tuftV (century o) X
lemma locale_val (X:Era G Lounge)(h:Auth k X)(v:CellR): Auth k (locale v X):= h.tuft _
lemma singless (P: TowerS G D)(x y:ℝ)(b:Cover)(o:CellR)(F:Rarity D)(p:0<x)(v:b∉ VisitsT F x y o): locale o (shoe P F x y b)=0:=by
    have he: wheelC x y b F.ψ o=0:=not_ne_iff.mp (mt (visiting p).mpr v)
    refine Prod.ext (funext fun n=>funext fun i=>funext fun j=>funext fun w=>?_) (funext fun i=>funext fun j=>funext fun w=>?_)
    · change P.1 n i j _ (wheelC x y b F.ψ o)=0; rw [he]; exact map_zero _
    change P.2 i j _ (wheelC x y b F.ψ o)=0; rw [he]; exact map_zero _
lemma shoreSum {S:Finset U}{X:U→ Era G Lounge}{a:U→ℝ}(p:CellR): locale p (∑ i∈ S,a i • X i)=∑ i∈ S,a i • locale p (X i):=by
    unfold locale tuftV; refine Prod.ext (funext (fun n=>?_)) (?_)
    · change ply _ _=_; simp only [Prod.fst_sum,Finset.sum_apply,Prod.smul_fst,Pi.smul_apply,map_sum,map_smul]
    change ply _ _=_; simp only [Prod.snd_sum,Prod.smul_snd,map_sum,map_smul]
lemma pupil_eye (k:ℕ)(P:TowerS G D)(F:Rarity D)(x y:ℝ)(o:CellR)(p:0<x) : locale o (pupil k P F x y)=∑ i∈VisitsT F x y o,drumB k x • locale o (shoe P F x y i):=by
   classical
   unfold pupil; rw [shoreSum]; exact Eq.symm (Finset.sum_subset (by intro i h; exact Finset.mem_of_mem_filter _ h) fun i _ v=>by rw [singless P x y i o F p v,smul_zero])

-- P Charge buds
abbrev OrbP (S:Patch)(F:Rarity D)(t y:ℝ)(o:CellR): ProfileW:= fun i=> saddleP S.L (VisitsT F t y o) (parentC S.L i)
lemma spiralC (S:Patch)(F:Rarity D)(x y:ℝ)(o:CellR)(p:Cover)(v:p∈VisitsT F x y o)(i:dock Cover α r)(u:ℕ): quoteT (OrbP S F x y o) u i≤9^u*hedge p 1 u i:=by
    let X:=OrbP S F x y o; let b:= tread Bank.terrain p i; let L:=S.L; let Q:=Ridge X i; have hv: ℕ := 0
    have hg: Q≤ b+8:=by
       apply Ridge.cap; intro j; let z:=(i j).1; let d:= Bank.terrain.gap (parentC L p) (parentC L z); apply (launchS L v (parentC L z)).trans
       have he: L.val*d≤ b+8*L.val:= (parent_stride p z).trans (Nat.add_le_add_right (leg_le Bank.terrain (stud p i) 0 j.succ) _)
       have hx:b ≤  L.val*b
          := le_mul_of_one_le_left (Nat.zero_le _) L.pos
       apply Nat.le_of_mul_le_mul_left (le_trans he (le_trans (Nat.add_le_add_right hx _) (le_of_eq (show L.val*b+8*L.val=L.val*(b+8) from by ring)))) L.pos
    refine (autumn_mono zero_le_one u hg).trans ?_; apply (autumn_tax zero_le_one ..).trans; simp only [show autumn 1 u 8=9^u by norm_num [autumn]]; exact le_of_eq (mul_comm ..)
lemma slopeP (F:Rarity D)(x y:ℝ)(o:CellR)(v:0<x)(h:x≤1)(p:Cover)(e:p∈ VisitsT F x y o)(i:dock Cover α r)(u:ℕ): hedge 0 x u i≤ (1+4*radiusH F x y)^u* hedge p 1 u i:=by
    apply (autumn_mono v.le u (move_cap Bank.terrain 0 p i)).trans ((autumn_tax v.le ..).trans ?_); rw [mul_comm (autumn _ u (tread _ p _))]
    have hp := reachFit F x y o v p e
    apply mul_le_mul _ (autumn_shrink v.le h ..) (zero_le_one.trans (autumn_pos v.le ..)) (by have ht:=fieldCap F x y; positivity)
    unfold autumn; exact pow_le_pow_left₀ (by positivity) (add_le_add_right hp _) _
lemma sing_charge (T: TowerS G D)(F:Rarity D)(x y:ℝ)(o:CellR)(p:Cover)(v:0<x)(h:x≤1)(l:Amplitude F B)(t:Fruit 0 1 i (T.2 k j) A): Fruit p 1 i ((locale o (shoe T F x y p)).2 k j) (B*A):=by
   let q:= wheelC x y p F.ψ o; let R: ChamberTen G (Vote D) j:= T.2 k j; let Q:= revolve p R; have hp: Fruit p 1 i Q A:= by simpa only [add_zero] using (Fruit.turn t p)
   have he (w:dock Cover (Hooks G) j) : ‖Q w q‖≤B*‖Q w‖:=by rw [mul_comm]; exact ((Q w).le_opNorm q).trans (mul_le_mul_of_nonneg_left (amplitudes_bound x y l v.le h o p) (norm_nonneg _))
   exact budget_minor (cap_scale hp l.1) (fun i=>mul_nonneg (hedge_nn zero_le_one _) (norm_nonneg _)) (fun i=>(mul_le_mul_of_nonneg_left (he i) (hedge_nn zero_le_one i)).trans_eq (by ring))
lemma dockSum (P Q:TowerS G D)(x y:ℝ)(d:Cover)(F:Rarity D)(o:CellR)(k j): (locale o (shoe (P-Q) F x y d)).2 k j = (locale o (shoe P F x y d)).2 k j- (locale o (shoe Q F x y d)).2 k j:=by funext v; rfl

section
variable (P Q:TowerS G D)(F:Rarity D)(x y z:ℝ)(p:On k P)(q:On k Q)(o:CellR)(u:ℕ)(v:0<x)(h:x ≤ 1)(t:Amplitude F B) {δ:ℝ}
include v h t in
lemma singT (t': YieldP 0 1 u A δ (P.2 e r) (Q.2 e r))(d:Cover) : YieldP d 1 u (B*A) δ ((locale o (shoe P F x y d)).2 e r) ((locale o (shoe Q F x y d)).2 e r):=by
   refine ⟨sing_charge P F x y o d v h t t'.wax,sing_charge Q F x y o d v h t t'.wane,?_⟩; rw [← dockSum,mul_assoc]; exact sing_charge (P-Q) F x y o d v h t t'.toll

def BasePrice (k:ℕ)(p:Rarity D)(x y:ℝ):ℝ:= (x^k)⁻¹*(5*radiusH p x y)^4
include v h in
lemma expanse (l:ℕ) (c:ℝ)(hc:0≤c): (∑ _i∈VisitsT F x y o, |drumB l x| * c) ≤ BasePrice l F x y * c:=by
    classical
    have hp:= drumC x v.le l; rw [abs_of_nonneg hp, Finset.sum_const,nsmul_eq_mul,←mul_assoc]; apply mul_le_mul_of_nonneg_right _ hc; unfold BasePrice
    have he : ((VisitsT F x y o).card:ℝ)*drumB l x ≤ (canvasM F x y).card *drumB l x := mul_le_mul_of_nonneg_right (by exact_mod_cast (show _ ≤ _ from Finset.card_filter_le ..)) hp
    apply he.trans; rw [mul_comm _ (drumB l x),drumB,mul_right_comm,mul_comm ((x^l)⁻¹)]; exact mul_le_mul_of_nonneg_right (census F x y v h) (by positivity)
include p q v h t
lemma census_br (t':∀ i ≤ e,∀ r:ℕ,YieldP 0 1 u A δ (P.2 i r) (Q.2 i r))(hx:0≤δ)(l:ℕ): Fringed k e u x (BasePrice l F x y*((1+4*radiusH F x y)^u*(B*A))) δ (locale o (pupil l P F x y)) (locale o (pupil l Q F x y)):=by
    refine ⟨locale_val _ (placed l F p ..) _, locale_val _ (placed l F q ..) _, hx,fun i r g=>?_⟩
    set C:=(1+4*radiusH F x y)^u*(B*A); set S:=VisitsT F x y o; have hh:=fieldCap F x y; have hz:0≤(1+4*radiusH F x y)^u:=by positivity
    have hC:= mul_nonneg hz (mul_nonneg t.1 (t' i g r).nn)
    have hp b (j:b∈ S): YieldP 0 x u C δ ((locale o (shoe P F x y b)).2 i r) ((locale o (shoe Q F x y b)).2 i r):=by
        let T:=(1+4*radiusH F x y)^u; have he:=singT P Q F x y o u v h t (t' i g r) b
        have heq {U: ChamberTen G ℝ r}{A:ℝ}(t:Fruit b 1 u U A): Fruit 0 x u U (T*A):= budget_minor (cap_scale t hz) (fun k=>mul_nonneg (hedge_nn v.le _) (norm_nonneg _)) (fun k=>(mul_le_mul_of_nonneg_right (slopeP F x y o v h b j k u) (norm_nonneg _)).trans_eq (by rw [mul_assoc]))
        refine ⟨heq he.wax,heq he.wane,?_⟩; unfold C; rw [mul_assoc]; exact heq he.toll
    rw [pupil_eye _ _ _ _ _ _ v,pupil_eye _ _ _ _ _ _ v]; simp only [Prod.snd_sum,Finset.sum_apply,Pi.smul_apply,Prod.smul_snd]; exact (YieldP.sum (S:=S) (fun i hi=>(hp i hi).μ (drumB l x)) v.le).step (expanse F x y o v h l C hC) hx
omit p q in
lemma orbFunds (L:Patch)(t':∀ i ≤ e,∀ r:ℕ,YieldP 0 1 u A δ (P.2 i r) (Q.2 i r))(hx:0≤δ)(l:ℕ): PaidMer e u (OrbP L F x y o) (locale o (pupil l P F x y)) (locale o (pupil l Q F x y)) (BasePrice l F x y*(9^u*(B*A))) δ:=by
   intro i r k; set C:=(9:ℝ)^u*(B*A); set S:=VisitsT F x y o; have hp:0≤(9:ℝ)^u:=by positivity
   let W:=OrbP L F x y o; have hv d (g:d∈ S): PromX W u C δ ((locale o (shoe P F x y d)).2 i r) ((locale o (shoe Q F x y d)).2 i r):=by
       have he:=singT P Q F x y o u v h t (t' i k r) d; have hh {U: ChamberTen G ℝ r}{A:ℝ}(f:Fruit d 1 u U A):Rent W u U (9^u*A):= budget_minor (cap_scale f hp) (fun i=>mul_nonneg (zero_le_one.trans (quoteT_pos i ..)) (norm_nonneg _)) (fun i=>(mul_le_mul_of_nonneg_right (spiralC L F x y o d g i u) (norm_nonneg _)).trans_eq (by rw [mul_assoc]))
       refine ⟨hh he.wax,hh he.wane,?_⟩; unfold C; rw [mul_assoc]; exact hh he.toll
   have hC:=mul_nonneg hp (mul_nonneg t.1 (t' i k r).nn)
   rw [pupil_eye _ _ _ _ _ _ v,pupil_eye _ _ _ _ _ _ v]; simp only [Prod.snd_sum,Finset.sum_apply, Pi.smul_apply, Prod.smul_snd]; exact (PromX.gather (S:=S) (fun i hi=>(hv i hi).μ (drumB l x))).stepX (expanse F x y o v h l C hC) hx
end
end YM.WilsonCoeffUV.Mer
