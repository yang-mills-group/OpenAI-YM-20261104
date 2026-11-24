import YM.MS.Book.Fields
/-! Move diagonal wave through periods/Evaluation and scale. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Book.Program
open Function Filter Set Finset Koszul Plane Cylinder Lab Convolve Lattice
open PowerSeries (coeff)
variable {A B I : Type}
-- labelled operations; move with Λ on log-link variables. need row. note `tuition_clock` unbounded rank.
def flag (S:Cn→ℂ) (V:A→Cn): Op A ℂ where
    toFun F l:= S (l.map V).prod *F l
    map_add' _ _:=funext fun _=>mul_add ..
    map_smul' _ _:=funext fun _=>mul_left_comm ..
lemma flag_Uses (S:Cn→ℂ)(V:A→Cn){s:Set A}{F:Raw A ℂ}(h:Uses s F): Uses s (flag S V F):= fun l i hi hI=> by simp [flag,h l i hi hI]
def pennant (S:Cn→ℂ)(V:A→Cn) : Cyl A ℂ→ₗ[ℂ] Cyl A ℂ:= ((flag S V).comp (Stack A ℂ).subtype).codRestrict (Stack A ℂ) (fun f=> by obtain ⟨s,hs⟩:=fromCyl f; exact packed (flag_Uses S V hs))
lemma pennantC (S:Cn→ℂ) (F:Cyl A ℂ)(U:A→Cn)(V:B→Cn)(P:B→A→ℂ)(hp:∀ i j,P i j≠0→U j=V i): flag S V (shade P F)=shade P (pennant S U F):= by
    have he {A:Type} (f:List A→ℂ)(U:A→Cn)(S:Cn→ℂ)(i:A) : D i (flag S U f)=flag (fun t=> S (U i*t)) U (D i f):= rfl
    have ht l : flag S V (shade P F) l=shade P (pennant S U F) l:= by
       induction l generalizing S F with
       | nil=> rw [shade_nil,flag]; change S _ * shade P F []= S _ *F.val []; rw [shade_nil]; rfl
       | cons i l ih=>
          obtain ⟨s,hs⟩:= fromCyl F; rw [D_eval i (flag _ _ _),he,shade_drop _ i F hs,deriv_lum _ i _ (s:=s) (flag_Uses S U hs),map_sum, Finset.sum_apply]; apply Finset.sum_congr rfl; intro j hj; by_cases ht:P i j=0; simp [ht]
          rw [map_smul,Pi.smul_apply,ih,← hp i j ht, show enter j (pennant S U F)=pennant (fun t=> S (U j*t)) U (enter j F) from rfl]; rfl -- h proof prop he
    exact funext ht
lemma pennant_ferry (r:A→B)(S:Cn→ℂ)(U:A→Cn)(V:B→Cn)(h:∀ i,U i=V (r i))(F:Cyl A ℂ): Ferry r (pennant S U F)=pennant S V (Ferry r F):= by
    refine Subtype.ext (Eq.symm (pennantC S F U V (way r) (fun i j hi=>?_))); rw [show i=r j from Classical.byContradiction fun hh=> hi (need _ hh),h]
def train (V:A→Cn) (n:ℕ): Cyl A ℂ→ₗ[ℂ] Cyl A ℂ:= pennant (coeff n) V
lemma train_v (V:A→Cn)(n:ℕ)(F:Cyl A ℂ): (train V n F).val=merit V n F.val:=rfl
lemma merited {k:ℕ}(x:A→Cn)(F:Cyl A ℂ){q:ℤ} (h:Limit F.val q): Limit (train x k F).val q:= fun l hl=> by simp [train_v,offer,h l hl]
def car (V:A→Cn): T (Cyl A ℂ)→ₗ[ℂ] T (Cyl A ℂ) where
    toFun F n:=∑ i∈antidiagonal n,train V i.1 (F i.2)
    map_add' F H:= by funext n; simp only [Pi.add_apply,map_add,Finset.sum_add_distrib]
    map_smul' c F:= by funext n; simp only [Pi.smul_apply,map_smul,RingHom.id_apply,Finset.smul_sum]
lemma rolls (F:T (Cyl A ℂ))(V:A→Cn)(n:ℕ): car V F n=∑ i∈antidiagonal n,train V i.1 (F i.2):=rfl
lemma formcost (r:A→B)(U:A→ Cn)(V:B→Cn)(h:∀ i,U i=V (r i))(F:T (Cyl A ℂ)): promote (Ferry r) (car U F)=car V (promote (Ferry r) F):= by funext l; rw [promised,rolls,rolls,map_sum]; simp_rw [train,pennant_ferry r _ _ _ h, promised]
-- stencils into mesh
variable (F:T (Seed A Cover ℂ))(V:A→Cn)(b: Bool)
def dotD (V:A→Cn) (F:T (Seed A Cover ℂ)):= car (V ∘ Prod.fst) F
lemma mission (n:Side) (k:ℕ) (F: Seed A Cover ℂ): duty b n (train (V∘Prod.fst) k F) = merit (V∘Prod.fst) k (duty b n F):= by
   let V': Mode A Cover→Cn:= V∘ Prod.fst; let V₁:Mode A (Site n)→Cn:=V∘Prod.fst; let Q:= train V₁ k; have h: shown n (train V' k F)=Q (shown n F):= pennant_ferry (post (wrap n)) (coeff k) V' V₁ (fun _=>rfl) F
   cases b; · change (shown n (train V' k F)).val=(Q (shown n F)).val; rw [h]
   change (sumHome (shown n (train V' k F))).val=(Q (sumHome (shown n F))).val; rw [h]; congr 1; rw [total_uses,total_uses,map_sum]; apply Finset.sum_congr rfl; intro i _; exact pennant_ferry (post (fun x=>i+x)) (coeff k) V₁ V₁ (fun _=>rfl) _
lemma grid (n:Side) : promote (duty b n) (dotD V F)=taxi (V ∘ Prod.fst) (promote (duty b n) F):= by unfold dotD; funext l; rw [promised,rolls,map_sum]; change _=∑ i∈antidiagonal l, merit _ _ (promote (duty b n) F _); simp_rw [mission,promised]
end YM.MS.Book.Program
