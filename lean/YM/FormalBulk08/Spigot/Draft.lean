import YM.FormalBulk08.Spigot.Guide
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Spigot
open Function Filter Lattice RG Laurent Bloch Exterior Wilson
open Reef Lava Gorge Mesa Shore Lotus Orb Wick Series Jets PowerSeries North Cork City Wine Flat Glide Bank Chapel Rift Kemp Dawn MeasureTheory
open Stationary hiding shine Rays
open scoped Topology ENNReal Matrix BigOperators Classical ContDiff
variable {I:Type*}{G:Gauge}{n:Side}{r t u e E D:ℕ}{A B C σ η:ℝ}
open Grail Precision Work.F03 Pose Tensor
open Planned.PrimaryIntegral295 Place Carrier
open scoped Matrix.Norms.Frobenius

-- exact mass packet cost including complete address & path
structure Cabin (D:ℕ)(I:Type)(G:Gauge)(r:ℕ) where
    atoms:I→Atom G r
    plus:I→Spigot.Halo D
    minus:I→Spigot.Halo D
    pulse:I→Studio D→ₗ[ℝ]ℝ
structure Energy {I:Type}(M:Cabin D I G r)(u:ℕ)(σ B:ℝ):Prop where
    plus:∀ i,Fleet (M.plus i)
    minus:∀ i,Fleet (M.minus i)
    income: SumBudget (fun i=>(M.atoms i).magnitude * Spigot.burse u (M.atoms i).length σ (M.plus i) (M.minus i)) B
    paper : ∀ i: I,∀ p:Studio D, M.pulse i p=record (M.plus i) (M.minus i) p
    actual : ∀ i,(M.atoms i).Invariant
variable (P:Dill)(Q:Herald)
section budget
def circ (o:Loc G 1)(i:P.Foils G r):ℝ:= herb (fame _) (0,o) (arctic G r (i.1.1,i.2))
private lemma sum_metre (o:Loc G 1)(hη:0<η):∃ K:ℝ,0≤K∧ ∀ A:ℝ,0≤A→∀ f:P.Foils G r→ℝ,(∀ i,0≤ f i)→ (∀ i,f i≤A*Real.exp (-η*circ P o i))→SumBudget f (K*A):= by
   let a:=η/2; have ha:0<a:=half_pos hη; let D(i:chain (edgeL G) r):=Real.exp (-a*herb (fame _) (0,o) i); let b:=∑' i,D i; let M:= (4:ℝ)^r * widthCost a r; have hh:0≤M:=mul_nonneg (by positivity) (zero_le_one.trans (widthCost_ge ha r)); have hx:0≤b:=tsum_nonneg fun i=>(Real.exp_pos _).le; refine ⟨b*M,mul_nonneg hx hh,fun A hA f hp ht=>?_⟩; let U:=arctic G r
   have hd: Summable D:= harvest o ha;have hg:= U.summable_iff.mpr hd
   have hs: SumBudget (fun w:chain Stoop r=> (∑ j:chain (hue G) r,D (U (w,j))) * (M*A)) (b*M*A):= by
      have hu (w:chain Stoop r): (∑' j:chain (hue G) r,D (U (w,j)))=∑ j:chain (hue G) r,D (U (w,j)):= tsum_fintype _; simp_rw [←hu]
      refine ⟨fun x=>mul_nonneg (tsum_nonneg (fun i=> (Real.exp_pos _).le)) (mul_nonneg hh hA),hg.prod.mul_right _,le_of_eq ?_⟩
      rw [tsum_mul_right]; change (∑' w,∑' x,(D ∘ U) (w,x)) * (M*A) = _; rw [←hg.tsum_prod]; simp only [comp_apply]; rw [Equiv.tsum_eq U D]; exact (mul_assoc b M A).symm
   apply budget_fan hp; apply budget_sigma (fun i=>Finset.sum_nonneg fun j _=>hp _); refine sum_tier hs (fun _=> Finset.sum_nonneg fun i _=>Finset.sum_nonneg fun j _=>hp _) (fun i=>?_) ; rw [Finset.sum_mul,Finset.sum_comm]; refine Finset.sum_le_sum (fun j _=> ?_)
   let d:ℝ:= herb (fame _) (0,o) (U (i,j));have hD:0≤d:=Nat.cast_nonneg _
   apply le_trans (Finset.sum_le_sum (s:=(Finset.univ: Finset (P.Hats i))) (g:=fun _=> A*Real.exp (-η*d)) (fun w _=>ht (⟨i,w⟩,j))); rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; have he:(4:ℝ)^r*(1+d)^r≤ M*Real.exp (a*d):= (mul_le_mul_of_nonneg_left (widthBill a ha r d hD) (by positivity : 0≤(4:ℝ)^r)).trans_eq (by rw [←mul_assoc]);
   · change _ ≤ D (U (i,j))*_ ; refine (mul_le_mul_of_nonneg_right ((Dill.foil_card P o _ _).trans he) (mul_nonneg hA (Real.exp_pos _).le)).trans_eq ?_; change _=Real.exp (-a*d)*(M*A); rw [show -a*d=a*d + (-η*d) by unfold a; ring, Real.exp_add]; ring
-- μ width and full polynomial+d exponent on generated invoice. choose positive before L for demands
private lemma advancing (P:Dill)(Q:Herald)(o:Loc G 1)(r u:ℕ)(hs:0<σ):∃ η M:ℝ,0<η∧0≤ M∧ ∀ i:P.Foils G r,rush u η (((P.chamber Q i).length:ℝ)+8) ≤ M *Real.exp ((σ/2)*circ P o i):= by
    let A:ℝ:=1+(r:ℝ)*Q.C; have ht:0≤(r:ℝ)*Q.C:= mul_nonneg (by positivity) Q.active.le;have hA:0<A:=by unfold A;linarith
    let s:=σ/(4*A); have he : 0<s:=by unfold s; positivity
    let H:= widthCost s u; have hH:= (widthCost_ge he u)
    refine ⟨s,H*Real.exp (2*s*(A+8)),he,mul_nonneg (zero_le_one.trans hH) (Real.exp_pos _).le,fun i=>?_⟩
    let d:ℝ:= circ P o i; have hd: 0 ≤ d:=Nat.cast_nonneg _; let K:ℝ:=(P.chamber Q i).length; have hk:0≤K:=Nat.cast_nonneg _; have hp : K ≤ A*(1+d):= (P.deline Q o i.1 (0:Tile (edgeL G) r) i.2).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (by change 0≤1+d;linarith))
    unfold rush; apply (mul_le_mul_of_nonneg_right (widthBill s he u _ (show 0≤ K+8 by linarith)) (Real.exp_pos _).le).trans; change H*Real.exp (s*(K+8))*_ ≤ (H*_)*Real.exp ((σ/2)*d); rw [mul_assoc,mul_assoc H,←Real.exp_add,←Real.exp_add]; apply mul_le_mul_of_nonneg_left (Real.exp_monotone _) (zero_le_one.trans hH); have hz:s*A=σ/4:= by unfold s; field_simp;
    change s*(K+8) + s*(K+8) ≤ _; nlinarith [mul_le_mul_of_nonneg_left hp he.le, congr_arg (· * d) hz]

def sols (i:P.Foils G r)(f:Studio D→ₗ[ℝ]Tile (edgeL G) r):Studio D→ₗ[ℝ]ℝ where
    toFun p:= P.shutter Q i (f p)
    map_add' p q:= by rw [f.map_add]; simp [Dill.shutter,Dill.oracle,add_mul]
    map_smul' a p := by rw [f.map_smul]; simp [Dill.shutter,Dill.oracle,mul_assoc]

lemma collected_bill (o:Loc G 1)(hs:0<σ)(r u D:ℕ) :∃ η K:ℝ,0<η∧0≤K∧∀ (f:Studio D→ₗ[ℝ] Tile (edgeL G) r)(A:ℝ),0≤A →(∀ p:Studio D,Knoxville (fame _) σ (0,o) (f p) (A*‖p‖)) → ∃ μ ν:P.Foils G r→_, Energy (Cabin.mk (P.chamber Q) μ ν (fun i=>sols P Q i f)) u η (K*A):= by
   let M:=reserve (picker G r); let F:ℝ:=Fintype.card (Brush D); have hm:0≤M:=pay_reserve _; have hF:0≤F:=Nat.cast_nonneg _
   obtain ⟨η,R,h,hR,I⟩:= advancing P Q o r u hs
   obtain ⟨K,hK,H⟩:= sum_metre P (r:=r) o (half_pos hs)
   refine ⟨η,K*(M*R*F),h,mul_nonneg hK (mul_nonneg (mul_nonneg hm hR) hF),fun f A ha hx=>?_⟩
   let V:= fun i:P.Foils G r=>A/Real.exp (σ*circ P o i)
   choose μ ν hμ hν hW hz using fun i:P.Foils G r=> address_account (V i) (div_nonneg ha (Real.exp_pos _).le) (sols P Q i f) fun p=> by
       change ‖P.shutter Q i (f p)‖≤ _;rw [Real.norm_eq_abs,Dill.shut_abs,← Real.norm_eq_abs]
       have ht:=penn_chill (arctic G r (i.1.1,i.2)) (hx p); rw [show V i * ‖p‖= A*‖p‖/Real.exp (σ*circ P o i) from (by unfold V;ring), le_div_iff₀ (Real.exp_pos _)]; exact ht
   refine ⟨μ,ν,hμ,hν,?_,hz,Dill.chamber_head P Q⟩
   rw [mul_assoc K]; apply H ((M*R*F)*A) (by positivity) _ (fun i=>?_ ) (fun i=>?_)
   · exact mul_nonneg (Finset.sum_nonneg (fun _ _=>abs_nonneg _)) (burse_below _ (Nat.cast_nonneg _) (hμ _) (hν _))
   let a:ℝ:=(P.chamber Q i).length; let m:=circ P o i
   have he : Spigot.burse u a η (μ i) (ν i)≤ R*Real.exp (σ/2*m)*(F*(V i)):= (burse_hot u (Nat.cast_nonneg _) h.le (hμ i) (hν i)).trans (mul_le_mul (I i) (hW i) (district_pos ..) (mul_nonneg hR (Real.exp_pos _).le))
   refine (mul_le_mul (Dill.chamber_mag P Q i) he (burse_below u (by positivity : 0≤((P.chamber Q i).length:ℝ)) (hμ _) (hν _)) hm).trans_eq ?_
   change M*(R*Real.exp (σ/2*m)*(F* (A/Real.exp (σ*m))))=M*R*F*A*Real.exp (-(σ/2)*m)
   rw [show -(σ/2)*m=σ/2*m-σ*m by ring,Real.exp_sub]; ring
end budget
end YM.FormalBulk08.Spigot
