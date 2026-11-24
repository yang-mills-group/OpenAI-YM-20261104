import YM.RG05Readout.Nuclear.Flurry
/-!
# Hermite end bells -- exact tensor at any finite demanded discrete petals

The number/spacings of all samples may depend on p and N. These sums do
NOT incur a toll in analytic gates; here only ANOTHER offline approximation
of the held profile, exact at those points, leaving states coherence checks
independent.Memory not feeding bulk.Stencil bound absolute for THIS one
 coefficient.Could choose different presentations in different seam layouts.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Nuclear
open Tensor Analysis Function Filter Set MeasureTheory Native Pulse Lattice
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {n m d k:ℕ}{E:Type}[TopologicalSpace E]
variable {V J:Type}[Fintype V][DecidableEq V]
local notation "U"=>Cloud V
local notation "W"=> Wave V
set_option quotPrecheck false
variable (s:V→ℕ)(Ω:Set E)(C:Allow V)(F:E→Wave V)
local notation "D"=> ∑ i:V,(s i+2)
local notation "N"=>4*Fintype.card V
local notation "G"=> V→Cover
local notation "Z"=>scoreQ V
variable (T: Finset (Cloud V))(S r:ℝ)(a:Cloud V)
noncomputable def interim (F:E→Wave V)(d:ℕ)(r S:ℝ)(x:U): E→Wave V:= ∑ j∈links r r x (foam V S r),triangleX d x (Z j r) r r F
local notation "Y"=> interim F d r S
omit [TopologicalSpace E] in
lemma torch (d:ℕ) (hr:0<r)(ht:‖a‖< S)(u:E): (interim F d r S a u).val =ᶠ[𝓝 a] ((originalQ F d S r u)-package d a (F u)).val:=by
    let L:=foam V S r; let f(i:G)(y):ℂ:= (bundle r (Z i r)).val y; let K(i:G)(y):ℂ:= f i y*(package d (Z i r) (F u)).val y
    have H: Continuous (fun z:U=>‖a-z‖):= (continuous_const.sub continuous_id).norm
    have hi: ‖a-a‖<r/4:=by rw [sub_self,norm_zero];positivity
    filter_upwards [H.continuousAt.eventually (gt_mem_nhds hi), continuous_norm.continuousAt.eventually (gt_mem_nhds ht)] with x hx he
    let z:= (package d a (F u)).val x; have hp(i): (triangleX d a (Z i r) r r F u).val x= K i x-f i x*z:=by
        change (bundle r a).val x * (f i x* (_ - (package d a (F u)).val x))=_
        rw [trifold a x r hr hx,one_mul,mul_sub]
    unfold interim; simp only [Finset.sum_apply, AddSubmonoidClass.coe_finsetSum]; rw [Finset.sum_subset (s₂:=L) (show links r r a L⊆ L from Finset.filter_subset _ _)]; rotate_left
    · exact fun i hi hP=> unpair S r r hr le_rfl a x i hi hP (package d (Z i r) (F u) -package d a (F u))
    simp_rw [hp]; rw [Finset.sum_sub_distrib,← Finset.sum_mul,show (∑ i∈ L,f i x)=1 from fair S r hr _ he,one_mul]; change _=(originalQ F d S r u).val x-z
    unfold originalQ; simp_rw [AddSubmonoidClass.coe_finsetSum,Finset.sum_apply]; rfl
omit [TopologicalSpace E] in
lemma drops (d:ℕ) (hr:0<r)(u:E)(x:U)(hx: 2*r<‖x-a‖): (interim F d r S a u).val x=0:=by
    unfold interim; simp only [Finset.sum_apply,AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_eq_zero fun i _=> ?_; change (bundle r a).val x * _=_; rw [bundle_die a x r hr hx,zero_mul]
-- sign admissions
omit [DecidableEq V] in
lemma Bouquet.inverse {p:E→Wave V}{t:ℝ}(hp:Bouquet s Ω C p t): Bouquet s Ω C (-p) t:=by
    induction hp with
    | empty=> rw [neg_zero]; exact Bouquet.empty
    | bloom f a t he ha hb hF hC=> let F:= joint Finset.univ f; let p:=fun x=>a x • F; rw [show -p=(fun x=>-a x • F) from funext fun x=> (neg_smul _ _).symm]; refine Bouquet.bloom (a:=fun x=>-a x) _ _ he.neg (fun x hx=>?_) hb hF hC; rw [norm_neg]; exact ha x hx
    | add _ _ hu hv=> rw [neg_add]; exact hu.add hv
    | permit he h hp ih=> exact ih.permit (fun i hi=>congr_arg Neg.neg (h hi)) hp -- implicit
noncomputable def striker (d:ℕ): E→Wave V:= -(∑ i∈T,interim F d r S i)
omit [TopologicalSpace E] in
lemma strike (d:ℕ) (x:E) (hr:0<r) (hv:∀ i∈T, ‖i‖< S) (ht:∀ i∈T,∀ j∈T,i≠j→ 2*r<‖i-j‖) (ha:a∈T)(n:ℕ)(hn:n ≤ d): pie (striker F T S r d x+(originalQ F d S r x)) (F x) n a:=by
    let f:= originalQ F d S r x; let g:= package d a (F x)
    suffices he : (striker F T S r d x+f).val =ᶠ[𝓝 a] g.val by
       exact ((he.iteratedFDeriv ℝ n).eq_of_nhds).trans (pol_cost a (F x) hn).symm
    have h(i:U) (hi:i∈T∧i ≠a): ∀ᶠ y in 𝓝 a, (interim F d r S i x).val y=0:=by
        let f(t):=‖t-i‖; have h':Continuous f:=(continuous_id.sub continuous_const).norm; filter_upwards [h'.continuousAt.eventually (lt_mem_nhds (show 2*r < f a from ht a ha i hi.1 hi.2.symm))] with x' hx; exact drops F S r i d hr x x' hx
    have he: ∀ᶠ y in 𝓝 a, ∀ i∈T,i ≠ a → (interim F d r S i x).val y=0:= T.eventually_all.mpr (fun i hi=> by by_cases H:i=a; exact Eventually.of_forall fun _ hf=> False.elim (hf H); exact (h i ⟨hi,H⟩).mono (fun x hx _=>hx))
    filter_upwards [torch F S r a d hr (hv a ha) x, he] with y hu ht
    unfold striker; rw [AddMemClass.coe_add,Pi.add_apply,Pi.neg_apply, Finset.sum_apply, NegMemClass.coe_neg, AddSubmonoidClass.coe_finsetSum,Pi.neg_apply,Finset.sum_apply, Finset.sum_eq_single a (fun i hi hx=> ht i hi hx) (by simp [ha])]; rw [hu]; change - (f.val y-g.val y)+ f.val y= g.val y; abel
lemma striker_cost (d:ℕ)(h:Stone d Ω F) {C' x₀:ℝ} (hφ:Plant Ω C F x₀)(hd:∀ u∈Ω, Tall (F u) (d+1) 1 C')(hc:0≤C')(hrP:2*r≤ x₀)(hr:0<r)(hx:r≤1)(hp:D< d+1):
   Bouquet s Ω C (striker F T S r d) ((T.card:ℝ)* (plot V 16).card * pellets s d 4*r*C'):=by
      have he:=Bouquet.all (F:=interim F d r S) T (fun i _=> one_frost s Ω C F C' _ h hc hφ r r hr le_rfl (by linarith) hrP hx hd hp.le i (foam V S r)); refine (he.inverse s Ω C).permit (fun i _=> by unfold striker; simp only [Pi.neg_apply,Finset.sum_apply]) ?_
      have ht: r^(d+1-D) ≤ r:=pow_le_pow_of_le_one hr.le hx (n:=d+1-D) (show 1 ≤ _ by omega)|>.trans_eq (pow_one _)
      refine le_trans ?_ (le_of_eq (b:=_) (show (T.card:ℝ)*(((plot V 16).card:ℝ)*(pellets s d 4*r*C'))=_ from by ring)); gcongr; exact pellets_good _ _
end YM.RG05Readout.Nuclear
