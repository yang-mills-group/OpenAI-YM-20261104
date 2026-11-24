import YM.WilsonComparison.Finite.Wick

/-!
# Identify the finite-site vertices, BEFORE subtracting the quadratic or projecting

The flip is K→-K **and B→-L**, all variables included; it intertwines the two
conventions (note that `Rack.main` is an *action*, while `W G` is for the exponent).
The output here is by repeated left symbol derivatives in the complete link and
ghost torus space. For any LocalRatio, not a hand-picked formal "Haar"
parameter. We will use the `1/2` on ALL bulk vertices (including Haar) in both
systems in evaluating the orbifold diagrams.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonComparison.Finite
open Function Filter Lattice Precision
open MS MS.Landau MS.Koszul MS.Native MS.Cylinder MS.Bare MS.Native.Chart
open MSBar MSBar.Bric MSBar.Loft MSBar.Inlay MSBar.Odom
open Bric.Coil
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius
variable {P : Type} {G : Gauge}
local notation "Ɛ" => tagPosition G P
local notation "pP" => Native.Draft.DotFlip (G:=G) (P:=P)
local notation "R0" => Complex.ofRealHom

def siteSign (x : LegPosition G P) : ℂ := kSign (tagPosition G P x).1.1

def relabel {A B : Type} (p : Sector A) (e : A≃B) : Coil p ℂ →ₗ[ℂ] Raw B ℂ where
  toFun x l:= x (l.map e.symm)
  map_add' _ _:= rfl
  map_smul' _ _:= rfl
lemma relabel_product {A B : Type} {p : Sector A} {p' : Sector B} {e : A≃B} (h : ∀ i,p' (e i)=p i)
    (x y : Coil p ℂ) : relabel p e (x*y)=MS.Koszul.product p' (relabel p e x) (relabel p e y) := by
  let L:= relabel p e
  have he b : p (e.symm b)=p' b := by rw [← h,e.apply_symm_apply]
  have hb (v:List B) : degree p (v.map e.symm)= degree p' v:= by
    induction v with|nil=>rfl|cons i l ih=>simp [he,ih]
  have hD i (F: Coil p ℂ) : Koszul.D i (L F)=L (Coil.D (e.symm i) F):=rfl
  have hP i (F: Coil p ℂ) : sign p' i (L F)= L (plane i F) := by
    ext l; change Koszul.cross _ _ * F _ = plane i F _
    rw [polar,cross_sting,← eq_band,hb]
  change L (x*y)= _; ext l; induction l generalizing x y with
  | nil => rw [nil_product]; exact tap_mul ..
  | cons i l ih=>
    change L _ _= product p' (L x) (L y) (i::l)
    rw [D_eval i (product p' _ _),D_product, D_eval i (L _), hD, Bric.Coil.mulD,map_add,
      Pi.add_apply, he, ih (Coil.D (e.symm i) x) y, ih (plane _ x) _, hD, hD,hP]; rfl

abbrev siteSymbol := relabel (A:=LegPosition G P) ø (tagPosition G P) ∘ₗ weft siteSign
lemma siteSymbol_mul (x y:Coil (ø (E:=Flit G (Edge P)) (B:=Flit G P)) ℂ) :
    siteSymbol (x*y)= product pP (siteSymbol x) (siteSymbol y) := by
  change relabel _ Ɛ (weft _ (x*y))=_
  rw [weft_mul]; exact relabel_product tagParity ..
lemma siteSymbol_read (x:Heave G (Edge P) P ℂ) (l : List (LightMode G P)) :
    siteSymbol x l=((l.map (fun i=> kSign i.1.1)).prod)* x (l.map (tagPosition G P).symm) := by
  change weft siteSign x _ = _; rw [wefts,List.map_map]; unfold siteSign; simp only [Function.comp_def,(Ɛ).apply_symm_apply]
lemma siteSymbol_rank (x:Heave G (Edge P) P ℂ) (r:ℕ):
    siteSymbol (rankn r x)= MS.Book.mask r (siteSymbol x) := by
  ext l; simp only [siteSymbol_read, rankn_read, List.length_map]; by_cases h : l.length = r
  · rw [if_pos h, MS.Book.enough _ (by omega : (l.length:ℤ)=(r:ℤ)),siteSymbol_read]
  rw [if_neg h,mul_zero, MS.Book.strange _ (by omega : (l.length:ℤ)≠(r:ℤ))]

section Bare
variable [Fintype P] [DecidableEq P] {r:ℕ}
lemma base_equal (k: G.ColorIndex) : Nexus.base G k= baseC k:= rfl
omit [Fintype P] in
lemma slab_equal (x: Flit G P) : slabQ x= priv x := by
  obtain ⟨i,x⟩:=x; ext1 j; rw [Inlay.slab]; simp [priv,Pi.single_apply]
omit [Fintype P] in
lemma direct_link (i:Flit G (Edge P)) : direction (Ɛ (Place.a i))= slabQ i:= (slab_equal i).symm
omit [Fintype P] in
lemma siteSymbol_var (i:LegPosition G P) :
    siteSymbol (Wind ø R0 (varC ℝ ø i)) = siteSign i • atLetter (Ɛ i) := by
  ext l; rw [siteSymbol_read,blows,seep_read,var_read]
  cases l with
  | nil=> simp [atLetter]
  | cons x l=> cases l with
    | cons i l=> simp [atLetter]
    | nil=> by_cases h : x = Ɛ i;
            · subst x; simp [siteSign, atLetter]
            have hx : (Ɛ).symm x ≠ i:= fun he=> h ((Ɛ).symm_apply_eq.mp he)
            simp [Ne.symm h,hx, atLetter]

lemma real_analytic (F : Loft.Chart.Grove (Chart.City G P)) :
    siteSymbol (Wind ø R0 (MSBar.Inlay.bare (I:=P) F))=
      MS.Cylinder.Taylor.ink direction F.val := by
  let K:=pathof G (Edge P) P
  let I₀(F:Loft.Chart.Grove (Chart.City G P)) := MS.Cylinder.Taylor.ink direction F.val
  change siteSymbol (Wind _ _ (K.shine F))= I₀ F
  ext l; induction l generalizing F with
  | nil=> simp [siteSymbol_read,K,blows,seep_read,Loft.Chart.Grove.Brook.lit0,I₀]
  | cons i l ih =>
    obtain ⟨x,rfl⟩:= (Ɛ).surjective i
    rw [siteSymbol_read,List.map_cons,List.prod_cons,List.map_cons,(Ɛ).symm_apply_apply,blows,seep_read];
    change _ * (Complex.ofReal (K.shine (Loft.Chart.Grove.dx (K.stream x) F) _))= _
    rw [_root_.mul_assoc]
    have ht (X:Loft.Chart.Grove (Chart.City G P)): (l.map (fun i=> kSign i.1.1)).prod * Complex.ofReal (K.shine X _)= I₀ X l := Eq.trans (siteSymbol_read (Wind ø R0 (K.shine X)) l).symm (ih X)
    have ha (v:LegPosition G P) (he:K.stream v=0)(hh:direction (Ɛ v)=0): I₀ (Loft.Chart.Grove.dx (K.stream v) F) l=0∧I₀ F (Ɛ v::l)=0 := by
      rw [he]; refine ⟨?_,congr_fun (MS.Cylinder.Taylor.ink_off _ hh F.val) l⟩
      unfold I₀
      rw [show (Loft.Chart.Grove.dx 0 F).val=0 from funext fun _=> map_zero _,MS.Cylinder.Taylor.ink_zero]; rfl
    rw [ht]; rcases x with (x|x)|(x|x)
    · change 1*_= MS.Cylinder.Taylor.ink direction (MS.Cylinder.Taylor.layer (direction (Ɛ (Place.a x))) F.val) l
      rw [one_mul,direct_link]; rfl
    · obtain ⟨H,L⟩:= ha (Place.k x) rfl rfl
      rw [show I₀ (Loft.Chart.Grove.dx (K.stream (Place.k x)) F) l=_ from H,mul_zero]; exact L.symm
    · obtain ⟨H,L⟩:= ha (Place.c x) rfl rfl
      rw [show I₀ (Loft.Chart.Grove.dx (K.stream (Place.c x)) F) l=_ from H,mul_zero]; exact L.symm
    · obtain ⟨H,L⟩:= ha (Place.l x) rfl rfl
      rw [show I₀ (Loft.Chart.Grove.dx (K.stream (Place.l x)) F) l=_ from H,mul_zero]; exact L.symm
end Bare

section Volume
open Odom.Book MS.Native.Wilsonian MS.Bare.Focus Cylinder.Lab MS.Native.Paint Inlay.Net
variable {n : Side} {K : ChartRatio G} (hk:LocalRatio K)
local notation "S" => Site n
local notation "bk" => Rack G n K hk

lemma gauge_vectors (x:Flit G S) : (deck n).fly (slabQ x) = loco (drive n) x := by
  rw [slab_equal]; rfl
lemma projector_color (x:Flit G P) (y : Lot G P) : stip x y=Native.projector x y := rfl
lemma costs_color (i j k:Flit G S) : (grit G S).price i j k=colorTerm G S i j k := by
  rw [grit_price,slab_equal,slab_equal,projector_color]; rfl

lemma mark_leg_c (j: Flit G S) :
    siteSymbol (Wind ø R0 (Loft.C (E:=Flit G (Edge S)) ℝ j))=(panel G S).spark j := by
  rw [Loft.C,siteSymbol_var, show siteSign (Place.c j : LegPosition G S)=1 from rfl,one_smul]; rfl
lemma mark_leg_k (j:Flit G (Edge S)) :
    siteSymbol (Wind ø R0 (Loft.K (B:=Flit G S) ℝ j))=(-1:ℂ) • atLetter ((Paper G S).dual ((panel G S).AId j)) := by
  rw [Loft.K,siteSymbol_var]; rfl
lemma mark_leg_L (j:Flit G S) :
    siteSymbol (Wind ø R0 (Loft.L (E:=Flit G (Edge S)) ℝ j))=(-1:ℂ) • atLetter ((Paper G S).dual ((panel G S).KId j)) := by
  rw [Loft.L,siteSymbol_var]; rfl
lemma source_parts (j:Flit G (Edge S)) :
    siteSymbol (Wind ø R0 (Loft.beam (deck n).chat j))=stone (glow G S) (loco (drive n)) j := by
  rw [Loft.beam, map_sum,map_sum]; unfold stone; simp_rw [map_mul,siteSymbol_mul,mark_leg_c]; apply Finset.sum_congr rfl; intro i _
  unfold Inlay.Net.chat; rw [real_analytic]; rw [Inlay.Net.spotG]; simp_rw [gauge_vectors]; rfl
lemma B_source (i:Flit G S) :
    siteSymbol (Wind ø R0 (Loft.rod (E:=Flit G (Edge S)) (grit G S) i))=Focus.shadow (panel G S) (colorTerm G S) i := by
  unfold Loft.rod Focus.shadow; rw [Wind_smul,map_smul,map_sum,map_sum];
  simp_rw [map_sum, Wind_smul,map_smul,map_mul,siteSymbol_mul, mark_leg_c,costs_color, Finset.smul_sum,smul_smul]
  refine Finset.sum_congr rfl fun j _=> Finset.sum_congr rfl fun k _=>?_
  change _ • product _ _ _=_; congr 1
  rw [show halve ℝ=1/2 from ?_]; · simp only [Complex.ofRealHom_eq_coe] ; push_cast; ring
  norm_num [halve]

lemma ropes_eq : siteSymbol (Wind ø R0 ((Rack G n K hk).main- MSBar.Inlay.bare (bk).toLuster.caseG))=
    -(Paper G S).hung (launch (glow G S) (colorTerm G S) (loco (drive n))) := by
  let R:=bk; let V: Flit G S→ Flit G (Edge S) → Heave G (Edge S) S ℝ:= (deck n).chat; let L:=grit G S
  let g:= ∑ i, Loft.K ℝ i * Loft.beam V i; let g':= ∑ i:Flit G S,Loft.L (E:=Flit G (Edge S)) ℝ i * Loft.rod L i
  rw [show R.main-Inlay.bare (bk).toLuster.caseG=g-g' by unfold main superb feeds; change _+g-g'-_ = _; abel]
  unfold g g'; rw [Bonded.hung,(panel G S).split_i]; simp_rw [map_sub,map_sum, map_mul, siteSymbol_mul,
    mark_leg_k,mark_leg_L,V,L, source_parts, B_source, launch_stone,launch_shadow,feeA, feeK]
  rw [neg_add]; simp [Finset.sum_neg_distrib]

lemma absolute_energy :
    siteSymbol (Wind ø R0 (Inlay.bare (I:=S) (bk).toLuster.caseG))=
      - Taylor.ink (glow G S).e0 (Chart.rent (drive n)) := by
  rw [real_analytic]; rw [show Chart.rent (G:=G) (drive n) = (-1:ℝ) • (bk).toLuster.caseG.val from ?_,
    Taylor.ink_smul _ (bk).toLuster.caseG.2]; · simp; rfl
  ext x; exact (Chart.original_W x).trans (by change _=(-1:ℝ)*_; rw [neg_one_mul]; rfl)

lemma site_action :
    siteSymbol (Wind ø R0 (-(Rack G n K hk).main))= Cylinder.Lab.docket n (Wilsonian.W G) := by
  have h:= ropes_eq hk (n:=n)
  rw [map_sub,map_sub,absolute_energy hk] at h
  rw [map_neg,map_neg, Wilsonian.witnessD]; unfold Sourced; rw [sub_neg_eq_add] at h; rw [eq_sub_of_add_eq h]; abel
lemma haar_action :
    siteSymbol (Wind ø R0 (Rack G n K hk).ash)= Cylinder.Lab.docket n (Wilsonian.H G) := by
  unfold Odom.Book.ash; rw [real_analytic,Wilsonian.shiftD]; change _=Taylor.ink direction (totalH (G:=G))
  apply Taylor.inkit; filter_upwards [eventually_all.mpr (fun i:Edge S => ((continuous_apply i).tendsto (0:Chart.City G S)).eventually (MS.Bare.Maurer.real_ratio hk))] with x hx
  exact Finset.sum_congr rfl fun i (_:i∈Finset.univ)=> congr_arg Real.log (hx i)
end Volume
end YM.WilsonComparison.Finite
