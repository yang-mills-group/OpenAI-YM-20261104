import YM.Contacts.Pulse.Deck
import YM.Next.FREE_KERNELS.Stock
import YM.Extension.UV.NativeBed
/-! An exact envelope theorem for changing two distinct CUT histories.
No derivative of a minimizing saddle's coordinates. Gives kinetic and actual
measure inputs to the all-order bridge and avoids quantitative sqrt estimates.
The recursion uniform width here SEES only normalized K, not off-Bianchi H. -/
noncomputable section
namespace YM.Pulse.Spine
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix
open Finset Bloch Laurent Push.AbsoluteSums Extra.Iteration MergeProof Next.Free Work.F08 Extension.UV.Linear
open scoped Classical Topology BigOperators NNReal ENNReal
variable {α β X Y Z : Type}{L c f n:Side} {F G K M: Row (TypeFace 2) (TypeFace 2)}
section mix
variable (r:ℝ)(Q:Matrix X Y ℝ) -- X coarse, Y fine
variable {A B : Matrix Y X ℝ} {C D:Matrix X X ℝ} {F G:Matrix Y Y ℝ}
      [Fintype X][DecidableEq X][Fintype Y]
include r Q
lemma opacity (h:F*A=Qᵀ*C)(j:G*B=Qᵀ*D)(he:Q*A=1-r • C)(hg:Q*B=1-r • D)(hF:Fᵀ=F)(hC:Cᵀ=C): Aᵀ*(F-G)*B=C-D:= by
  have hy : Aᵀ*F=C*Q := by rw [←hF,← Matrix.transpose_mul,h,Matrix.transpose_mul,hC,transpose_transpose]
  rw [Matrix.mul_sub, Matrix.sub_mul,hy, Matrix.mul_assoc, Matrix.mul_assoc,j,hg, Matrix.mul_sub,Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc Aᵀ,← Matrix.transpose_mul,he, transpose_sub,transpose_one, transpose_smul,hC,Matrix.sub_mul,Matrix.one_mul, Matrix.smul_mul]; abel
end mix
abbrev krow := KrowSeries
abbrev voyage (L : Side) := Cross L (TypeFace 1) (TypeFace 1)
def portfolio (F G: Row (TypeFace 2) (TypeFace 2)):= minusRows (krow F) (krow G)
def keconomic (F G: Row (TypeFace 2) (TypeFace 2)):= both (plane (portfolio F G))
lemma k_capacity (h:Whole F) : Whole (krow F):= ((Whole.boundary 1).flipped.prod h).prod (Whole.boundary 1)
lemma pension (h:Whole F)(j:Whole G) (c:Side): (portfolio F G).acts c=Precision.K (F.acts c)-Precision.K (G.acts c) := ((k_capacity h).less (k_capacity j) c).trans (by unfold krow; rw [Krow_acts _ h,Krow_acts _ j])
lemma pem (n:Side)(h:(F.acts n)ᵀ=F.acts n): (Precision.K (F.acts n))ᵀ= Precision.K (F.acts n):= by simp [Precision.K,transpose_mul,h,Matrix.mul_assoc]
-- stripped from page_rear
lemma cross_symbol (p:Momentum)(i:ℕ)(h:star p=p): (symbol i (-p))ᵀ=(symbol i p)ᴴ:= by
  ext a b
  simp only [symbol,wedge,quanta h,Matrix.transpose_apply,Matrix.conjTranspose_apply,Matrix.sum_apply,Matrix.smul_apply,star_sum,smul_eq_mul,star_mul,Pi.star_apply]
  apply sum_congr rfl; intro i _; rw [mul_comm]; congr 1
  unfold Exterior.left; simp only [Matrix.of_apply]; split
  next h=> split <;> simp [parity]
  simp
lemma ship_core (h: Whole F)(p:Momentum)(hp:star p=p): (krow F).read p= dcross F p := by
  unfold krow KrowSeries; have hB:= Whole.boundary 1; rw [(hB.flipped.prod h).read hB hp,hB.flipped.read h hp,read_opposite _ hp,Exterior.reading,dcross,cross_symbol p 1 hp]
-- read ident exact krow symbol
variable {σ η:ℝ≥0}{p:Momentum}{a b:ℝ}
lemma both_publish (R:Row α α): author (extract (both (plane R)))=both (plane R):= relocate _ (by intro x z; simp [both,plane])
def singular : Tailor 1≃Cover := ⟨fun z i=> z (0,i), fun z i=>z i.2,fun z=> by ext ⟨j,k⟩; exact congr_arg z (Prod.ext (Subsingleton.elim _ _) rfl),fun z=>rfl⟩
lemma tear_both (R:Row α α)(b:Breed 1 α) (p: Space 1): Laurent.read (pale (extract (both (plane R)) b)) p= R.read (p ∘ stick 0) (b 0) (b 1):= by
  unfold Laurent.read Row.read; rw [Matrix.of_apply,Laurent.read,← singular.tsum_eq]; apply tsum_congr; intro z
  have h : mode p z= mode (p∘stick 0) (singular z):= by unfold mode; rw [Fintype.sum_prod_type]; simp only [Fin.sum_univ_one]; rfl
  rw [h]; congr 1; simp only [pale,extract,Function.comp_apply, Complex.ofRealCLM_apply,plane,both,publish,legLane,Fin.cons_zero,zero_add, sub_zero]; rfl
lemma vessel_age (hF:Whole F)(hG: Whole G)(h: F.read 0=G.read 0): softRank 3 (keconomic F G) := by
  intro b p
  have hx (x y): Rays 1 (fun i:Corn Axis=> F.read (axes i) x y-G.read (axes i) x y):= by
    obtain ⟨t,C,ht,hF⟩:=hF; obtain ⟨s,A,hs,hG⟩:= hG
    exact (rays_at_zero (AnalyticAt.sub ((price_step_metric ht hF x y).analytic_real _) ((price_step_metric hs hG x y).analytic_real _))).mpr (by simp [axes_origin,h])
  apply (bed_gain F G hx (b 0) (b 1) (p∘stick 0)).congr_left (fun j=> ?_)
  simp only [keconomic,Function.comp_apply,tear_both]; rw [show axes (j • p) ∘ stick 0= axes (j • (p ∘ stick 0)) from rfl,portfolio,read_less (k_capacity hF).safe (k_capacity hG).safe (axes_real _),Matrix.sub_apply,ship_core hF _ (axes_real _),ship_core hG _ (axes_real _)]

lemma from_both {R:Row α α} (h:Rooted (terrain σ α) (both (plane R)) a) : R.strip σ a := by
  intro x y; have he v : size (singular.symm v)=Laurent.size v := by unfold size; rw [Fintype.sum_prod_type]; simp only [Fin.sum_univ_one]; rfl
  apply budget_map (export_price (t:=1) (η:=σ) h ![x,y] (by simp)) singular.symm singular.symm.injective (fun i=> ?_)
  rw [he]; simp only [extract,Function.comp_apply,both,publish,plane,legLane,Fin.cons_zero,zero_add, sub_zero]; rfl
lemma arrive_both {R:Row α α}[Fintype α] (h:R.strip σ a)(hz:0≤a) (hp:(2*η:ℝ)≤σ): Rooted (terrain η α) (both (plane R)) (Fintype.card (Breed 1 α)*a) := by
  have hZ (b: Breed 1 α): Width σ a (extract (both (plane R)) b):= by
    apply budget_map (h (b 0) (b 1)) _ singular.injective (fun i=> ?_); simp only [extract,Function.comp_apply,both,publish,plane,legLane,Fin.cons_zero,zero_add, sub_zero]; rw [show size i=size (singular i) from ?_]; · rfl
    unfold size; rw [Fintype.sum_prod_type]; simp only [Fin.sum_univ_one]; rfl
  let P:= fun b:Breed 1 α=> flag b (extract (both (plane R)) b)
  refine Eq.mp ?_ (massSum (F:=P) fun i=> flag_price (b:=i) (hZ i) hp); rw [show (fun x=>∑ i,P i x)=_ from funext (fun x=> (authors _ x).symm.trans (congr_fun (both_publish R) x))]; simp

-- PRICE of structural sqrt stage same choice, diagonal.
lemma steadfast (hF: Whole F)(hG:Whole G)(hM: Whole M)(hK:Whole K){L:Side}{R R': voyage L}
    {c f:ℕ→Side}(hm:Tendsto (fun j=>(c j).val) atTop atTop) (S:∀ j,StepData (c j) (f j)) (hS:∀ j,(S j).ratio.count=L)
    (H:∀ j (P Q:voyage (S j).ratio.count), HEq R P → HEq R' Q → Inputs (S j) (installed (S j).ratio P) (F.acts (f j)) (M.acts (c j)) ∧
       Inputs (S j) (installed (S j).ratio Q) (G.acts (f j)) (K.acts (c j)))
    (he:∀ n,(F.acts n)ᵀ=F.acts n)(hj:∀ n,(M.acts n)ᵀ=M.acts n)
    (hp:Rooted (terrain σ (TypeFace 1)) (keconomic F G) a)(hv:(η:ℝ)/(L.val:ℝ)≤σ)(hP:Row.strip R η b)(hQ: Row.strip R' η b)(hb:0≤b):
    keconomic M K = allAt ![install R,install R'] (keconomic F G) := by
  have hw (p:Fin 2): Weirs (access L η) (![install R,install R'] p)
      ((L.val:ℝ)^4*(Fintype.card (TypeFace 1))*beamPrice η b) (Fintype.card (TypeFace 1)*beamPrice η b):= by fin_cases p; exact flow_price hP hb; exact flow_price hQ hb
  have hZ : Rooted (terrain η (TypeFace 1)) (allAt ![install R,install R'] (keconomic F G)) (((L.val:ℝ)^4*(Fintype.card (TypeFace 1))*beamPrice η b*a)*(Fintype.card (TypeFace 1)*beamPrice η b)):= by
    refine all_root hp (influx hv) hw (fun i=> ?_) ?_; · letI : DecidableEq (Fin 2) := fun a b=>Classical.propDecidable (a=b); simp
    unfold beamPrice; have hh:=hp.cash; positivity
  obtain ⟨z,C,hz,hC⟩:= (k_capacity hM).minus (k_capacity hK); lift z to ℝ≥0 using hz.le; have hc : 0≤C:= Cost.nonneg (hC (coord (0:Axis)) (coord 0))
  apply shadow_compare (k:=fun j=> both ((portfolio M K).acts (c j))) hm (arrive_both (R:=portfolio M K) (η:=z/2) hC hc (by push_cast; linarith)) hZ; intro i; refine ⟨title (row_ship ..),?_⟩
  suffices he' : ∀ (c f:Side)(S:StepData c f)(g:Ratio c f)(hg:S.ratio=g)(hu:g.count=L), (∀ X Y:voyage S.ratio.count, HEq R X → HEq R' Y → Inputs S (installed S.ratio X) (F.acts f) (M.acts c) ∧ Inputs S (installed S.ratio Y) (G.acts f) (K.acts c)) → Shadow (lower c) (allAt ![install R, install R'] (keconomic F G)) (both ((portfolio M K).acts c)) by exact he' _ _ (S i) (S i).ratio rfl (hS i) (H i)
  clear hm i hS H S
  intro c f S g hg hu HX; subst g L
  obtain ⟨h1,h2⟩:= HX R R' HEq.rfl HEq.rfl
  have HT : ∀ j:Fin 2, Trails (lower f) (lower c) (![install R,install R'] j) (![installed S.ratio R,installed S.ratio R'] j):= by intro j; fin_cases j; exact st_new ..; exact st_new ..
  have hh:= basin (title (row_ship (portfolio F G) f)) HT hp (influx hv) hw
  suffices hx : both ((portfolio M K).acts c)=allAt ![installed S.ratio R,installed S.ratio R'] (both ((portfolio F G).acts f)) by rw [hx]; exact hh
  funext y; rw [fasten,pension hM hK,pension hF hG]; exact Eq.symm (congr_fun (congr_fun (opacity S.kernel.penalty⁻¹ (mean S) h1.primal h2.primal h1.dual h2.dual (pem f (he f)) (pem c (hj c))) (y 0)) (y 1))
end YM.Pulse.Spine
