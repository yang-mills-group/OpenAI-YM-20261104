import YM.SchemeConversionRG11.Maxwell.SinglePeel

/-! # Attach a fresh color thread -/

set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.Corona
open Function Filter Maxwell Maxwell.Free Wick Tensor Set MvPolynomial
open scoped BigOperators ComplexOrder

variable {G : Gauge} {n m k : ℕ} {ι : Type*} [Fintype ι] {X : Points n} {a y : Fin n}

def assayed (p : ι → ℂ) (W : ι → Fin n → WickPol G) (X : Points n) := ∀ (r : Flavor 0) (b : E4), Points.cons b X ∈ conf _ → ∑ i:ι,p i*bookend X b (W i) (team G r r)=0

lemma pay_over {k l : ℕ} (p : ι→ℂ) (W : ι→Fin n→WickPol G) (h : ∀ i,W i a∈ shelf G l) (D : Echo k) (E : Echo m) (H : k>l) : payable X p W a y D E=0 := by
  unfold payable; apply Finset.sum_eq_zero; intro i _; apply Finset.sum_eq_zero; intro b _; unfold pay; rw [wield_at]; change p i * wield (moment _ _) _ _ (update _ _ (rip D b _))=_; rw [rip_none _ _ (h _) H, MultilinearMap.map_coord_zero _ a (update_self ..),mul_zero]

variable {Param : Type*}

/-- Any read family whose nonzero charges can be traded for arbitrary y-end reads
by varying its parameter. -/
lemma propel (C₀ : G.ColorIndex) (p : ι→ℂ) (W : Param→ι→Fin n→WickPol G) (hx : X ∈ conf _) (ha : a≠y)
    (N : Fin n→ℕ) (hn : N y=0) (hw : ∀ s i b,W s i b∈ shelf G (N b)) (h : ∀ s, assayed p (W s) X)
    (transfer : ∀ (l : ℕ) (D : Echo l) (E : Echo 0), E≠0 → (∀ s,payable X p (W s) a y D E=0) →
      ∀ s, ∀ E' : Echo 0,payable X p (W s) a y D E'=0)
    (D : Echo k) (E : Echo 0) (s : Param) : payable X p (W s) a y D E=0 := by
  classical
  let Holds (k : ℕ) := ∀ (D : Echo k) (E : Echo 0) s, payable X p (W s) a y D E=0
  have H : ∀ j : ℕ, ∀ i : ℕ,N a < i+j → Holds i := by
    intro j; induction j with
    | zero => intro i hi D E s; apply pay_over p (W s) (fun _ ↦ hw s _ _) D E (by omega)
    | succ j ih =>
      intro k hK D E s
      rcases lt_or_ge (N a) k with he|he
      · exact ih k (by omega) D E s
      let L := (priceL (k:=k) X p (W s) a y).flip E
      have hl : L=0 := by
        refine LinearMap.ext_on (spreads C₀ (disperses hx) ha _) (fun D hA ↦ ?_)
        obtain ⟨d,r,hh,H',rfl⟩ := hA
        exact transfer k _ _ H' (fun s ↦ peel C₀ p (W s) N r hx ha (hw s) hn (h s r) k he
          (fun l hl D E ↦ ih l (by omega) D E s) hh) s E
      exact LinearMap.congr_fun hl D
  exact H (N a+1) k (by omega) D E s

def welcome (p : ι→ℂ) (W : ι→Fin n→WickPol G) (X : Points n) (a y : Fin n) (D : Echo k) (r : Flavor 0) :=
    ∑ i:ι,∑ j:G.ColorIndex,p i * moment G X (update (hit D j a (W i)) y (bit r j))
lemma bit_plus (r s : Flavor k) (i : G.ColorIndex) : bit (r+s) i=bit r i+bit s i := by
  obtain ⟨L,h⟩ := symbol_linear (G:=G) k
  unfold bit; rw [map_add,← h]; exact map_add L _ _
lemma invite_plus (p : ι→ℂ) (W : ι→Fin n→WickPol G) (D : Echo k) (r s : Flavor 0) : welcome p W X a y D (r+s)=welcome p W X a y D r+welcome p W X a y D s := by
  simp_rw [welcome,bit_plus,MultilinearMap.map_update_add,mul_add,Finset.sum_add_distrib]
lemma hit_update (W : Fin n→WickPol G) (ha : a≠y) (D : Echo k) (i : G.ColorIndex) (v : WickPol G) :
    hit D i a (update W y v)=update (hit D i a W) y v := by unfold hit; rw [update_of_ne ha,update_comm ha.symm] -- check
lemma inviting (p : ι→ℂ) (W : ι→Fin n→WickPol G) (ha : a≠y) (r : Flavor 0) (D : Echo k) (E : Echo 0) :
    payable X p (fun i ↦ update (W i) y (team G r r)) a y D E= (2*E r) * welcome p W X a y D r := by
  unfold payable welcome; simp only [pay_hits, hit_update _ ha, Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [hit, update_self,update_idem, rip_team,MultilinearMap.map_update_smul,smul_eq_mul,mul_left_comm]
lemma shelf_frame (W : ι→Fin n→WickPol G) : ∃ n' : ℕ, ∀ i j,W i j∈ shelf G n' := by
  classical
  choose f hf using fun i j ↦ cap_exists (W i j)
  refine ⟨Finset.univ.sup (fun p:ι×Fin n ↦ f p.1 p.2), fun i j ↦ ?_⟩
  apply shelf_support.mpr
  exact fun w hw s h ↦ (shelf_support.mp (cap_shelf _ (hf i j)) w hw s h).trans (Finset.le_sup (f:=fun p : ι×Fin n ↦ f p.1 p.2) (b:=(i,j)) (Finset.mem_univ _))
lemma track_live : ∃ E : Echo 0,E ≠ 0 := by
  by_contra! hh
  let L : Echo 0 := Complex.ofRealCLM.toLinearMap.comp (Module.Dual.eval ℝ (Sheet 0) (blade 0 1 1))
  have ht := LinearMap.congr_fun (hh L) (cell 0 1)
  change (↑(cell 0 1 (blade 0 1 1)):ℂ)=0 at ht; rw [cell_price] at ht; norm_num [wedge,Matrix.one_apply] at ht
lemma all_invited {p : ι→ℂ} {W : ι→Fin n→WickPol G} {D : Echo k} (ha : a≠y) {E : Echo 0} (he : E≠0) (H : ∀ r : Flavor 0, payable X p (fun i ↦ update (W i) y (team G r r)) a y D E=0) :
    ∀ r, welcome p W X a y D r=0 := by
  choose u hu using (show ∃ r, E r≠0 by by_contra! ht; exact he (LinearMap.ext ht))
  have hh (r) (hr : E r≠0) : welcome p W X a y D r=0 := by
    have H := H r; rw [inviting p W ha] at H; exact (mul_eq_zero.mp H).resolve_left (mul_ne_zero (by norm_num) hr)
  intro r; by_cases h : E r=0
  · have hh' := hh (r+u) (by rwa [map_add,h,zero_add]); rwa [invite_plus,hh u hu,add_zero] at hh'
  exact hh r h
lemma invite (C₀ : G.ColorIndex) (p : ι→ℂ) (W : ι→Fin n→WickPol G) (hx : X∈conf _) (ha : a≠y)
    (h : ∀ (r : Flavor 0), assayed p (fun i ↦ update (W i) y (team G r r)) X)
    (D : Echo k) : ∀ r, welcome p W X a y D r=0 := by
  obtain ⟨v,hv⟩ := shelf_frame W
  let N : Fin n→ℕ := update (fun _ ↦ v) y 0
  let V := fun (r : Flavor 0) i ↦ update (W i) y (team G r r)
  have he (r i b) : V r i b∈ shelf G (N b) := by
    rcases eq_or_ne b y with hb|hb
    · subst b; simp only [V,N,update_self]; unfold team; exact Submodule.sum_mem _ fun j _ ↦ Subalgebra.mul_mem (Rack G 0) (symbol_shelf (flavor 0 j r) le_rfl) (symbol_shelf (flavor 0 j r) le_rfl)
    simp only [V,N,update_of_ne hb]; exact hv i b
  obtain ⟨E,hE⟩ := track_live
  refine all_invited ha hE (fun r ↦ propel C₀ p V hx ha N (update_self ..) he h ?_ D E r)
  intro l D E hh hr r Z
  exact (inviting p W ha r D Z).trans (by rw [all_invited ha hh hr r,mul_zero])

end YM.SchemeConversionRG11.Corona
