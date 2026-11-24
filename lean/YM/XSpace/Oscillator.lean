import YM.XSpace.Ruffle

/-!
# Infrared transport costs from one population of ordinary orbits

First-order only. Input an ordinary Cov on arbitrary period Rings. We are not assuming
that incidence weights from polynomial parity are convergent or priced, so prove a
small summation lemma once in collective setup. Work on total energy edges, no denominator.
Fixed cover polynomials and all translated positions. Profile arithmetic not needed yet.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Outline
open Function JetGauge Lattice RG Wilson Source Source.Drops Finsupp
open Next.Rank.Normal MvPolynomial Contraction Chart2
open scoped Topology BigOperators
variable {G:Gauge}{J:Type*}{R:J→Type*} [∀ i,AddCommGroup (R i)][∀ i, One (R i)] {Z:Type*} {S:Type*}[AddCommGroup S][One S]
structure Given (G:Gauge)(S:Type*)[AddCommGroup S][One S] where
  site : Chart ℤ S
  zero : site.site 0=0
  grant : JetGauge.Cov (Bone G S)
  goal : ℕ → Four S → Four S → Prop  -- `goal m mark integral`
namespace Given
variable (g:Given G S)
def points (x:Four S):Chart ℤ S:= g.site.shift x
@[simp] lemma gone (x:Four S): (g.points x).site 0=x:=by rw [points, Chart.shift_at,g.zero,zero_add]
abbrev burn (x : Four S) : Bone G ℤ → Bone G S:= (g.points x).roll
abbrev front (x:Four S) (i:Wing G ℤ) : Wing G S:= (((g.points x).site i.1.1,i.1.2),i.2)
def jingle (x:Four S) (i:Wing G ℤ):= ringBell (g.front x i)
lemma tick (x:Four S)(K:poly (Wing G ℤ)): (g.points x).pull (score G ℤ K)=exchange (g.jingle x) K:=by
  change (((g.points x).pull).comp (score G ℤ)) _=_
  congr 1; ext1 i; simp only [AlgHom.comp_apply,score,exchange_x]; exact ring_shift ..

def chirp (u : Bone G S)(p: Wing G S): ℂ:= Finsupp.linearCombination ℂ (g.grant.cov u) (ringBell p)
def reacts (i: Wing G ℤ) (j: Bone G ℤ)(x y:Four S):= g.chirp (g.burn y j) (g.front x i)
end Given
abbrev saving (k:ℕ):ℝ:= (1+(k:ℝ))⁻¹
lemma saving_ok (k):0<saving k:=by unfold saving; positivity
structure Society (F: ∀ i:J,Given G (R i)) :Prop where
  every : ∃ C:ℝ, 0<C ∧∀ i (j k:Bone G (R i)), ‖(F i).grant.cov j k‖≤ C
  single (j k): ∃ C:ℝ,0<C∧ ∀ i,∀ (x y:Four (R i)),∀ n:ℕ,(F i).goal n x y → ‖(F i).reacts j k x y‖≤ C * saving n
  energy (j k): ∃ C:ℝ,0<C∧∀ i,∀ x:Four (R i),∀ s:Finset (Four (R i)), ∑ y∈s, ‖(F i).reacts j k x y‖^2 ≤ C
  color (i) (p q: Bone G (R i)) : p.2 ≠ q.2 → (F i).grant.cov p q=0
variable (F: ∀ i:J,Given G (R i))

-- Core uniform real-norm bound for any stencil evaluation via multiple shifted mark anchors.
-- Local finite subset sums. Occurrences future.
def Quotation (p: ∀ i:J,(Z→Four (R i))→ℂ):Prop:=∃ C:ℝ, 0<C∧∀ i z,‖p i z‖≤C
namespace Quotation
variable {p q : ∀ i:J,(Z→Four (R i))→ℂ}
omit [∀ i,AddCommGroup (R i)][∀ i,One (R i)] in
lemma sum {ω:Type*}(s:Finset ω)(w:ω→∀ i:J,(Z→Four (R i))→ℂ)(h:∀ i∈s,Quotation (w i)):
    Quotation (fun i z=>∑ k∈s, w k i z):=by
  classical induction s using Finset.induction_on with
  | empty=> simp only [Finset.sum_empty]; exact ⟨1,zero_lt_one, by simp⟩
  | insert i s hi ih=> simp_rw [Finset.sum_insert hi]; obtain ⟨C,hC,H⟩:= h i (by simp); obtain ⟨D,hD,K⟩:= ih (fun j hj=> h j (by simp [hj])); exact ⟨C+D,by positivity,fun k z=> (norm_add_le ..).trans (add_le_add (H k z) (K k z))⟩
lemma const (J Z:Type*) {R:J→Type*}(t:ℂ): Quotation (fun (i:J) (_:Z→Four (R i))=>t):=⟨‖t‖+1,by positivity,by intros; linarith⟩
omit [∀ i,AddCommGroup (R i)][∀ i,One (R i)] in
lemma plus (h:Quotation p)(g:Quotation q):Quotation (p+q):=by obtain ⟨C,hC,H⟩:=h; obtain ⟨D,hD,K⟩:=g; exact ⟨C+D,by positivity,fun k z=> (norm_add_le ..).trans (add_le_add (H k z) (K k z))⟩
omit [∀ i,AddCommGroup (R i)][∀ i,One (R i)] in
lemma mul (h:Quotation p)(g:Quotation q):Quotation (fun i z=>p i z*q i z):=by obtain ⟨C,hC,H⟩:=h; obtain ⟨D,hD,K⟩:=g; refine ⟨C*D,by positivity,fun k z=>?_⟩; rw [norm_mul]; gcongr <;> first | positivity | apply H | apply K
end Quotation
open Given
-- marks canvas. keep all footprint strings to reference finite support if expanding
abbrev Shadow := poly (Z × Bone G ℤ)
abbrev Music := poly (Z × Wing G ℤ)

def jump (g:Given G S)(z:Z→Four S)(i:Z×Bone G ℤ): Bone G S:= (g.points (z i.1)).roll i.2
def motor (g:Given G S)(z:Z→Four S): Shadow (Z:=Z) (G:=G) →ₐ[ℂ] St S G:= rename (jump g z)
lemma motor_at (g:Given G S)(z:Z→Four S)(s:Z)(p:St ℤ G): motor g z (rename (Prod.mk s) p)=(g.points (z s)).pull p:=by
  unfold motor Chart.pull; rw [rename_rename]; rfl

def pattern (i:Z×Wing G ℤ): (Z×Bone G ℤ) →₀ℂ := embDomain (Function.Embedding.sectR i.1 (Bone G ℤ)) (ringBell i.2)
-- compose rings

def toot (g:Given G S)(z:Z→Four S)(i:Z×Wing G ℤ): Bone G S→₀ℂ:= g.jingle (z i.1) i.2
def shroud (g:Given G S)(z:Z→Four S): Music (Z:=Z) (G:=G) →ₐ[ℂ] St S G:= exchange (toot g z)
lemma shroud_turn (g:Given G S)(z:Z→Four S)(j:Z)(p:poly (Wing G ℤ)): shroud g z (rename (Prod.mk j) p)=(g.points (z j)).pull (score G ℤ p):=by
  rw [tick]; suffices h : (shroud g z).comp (rename (Prod.mk (β:=Wing G ℤ) j))=exchange (Given.jingle g (z j)) from DFunLike.congr_fun h _
  ext1 i; rw [AlgHom.comp_apply,rename_X,shroud,exchange_x,exchange_x]; rfl

def film := exchange (fun (i:Z×Wing G ℤ)=> pattern i)
lemma operate (g:Given G S)(z:Z→Four S)(p:Music): motor g z (film p)= shroud g z p:=by
  suffices h : (motor g z).comp film=shroud g z from DFunLike.congr_fun h _
  ext1 i; rcases i with ⟨j,k⟩; rw [AlgHom.comp_apply,film,exchange_x, ← show rename (Prod.mk j) (glyph (ringBell k))=glyph (pattern (j,k)) from ?_,motor_at,ring_shift,shroud,exchange_x]; rfl
  unfold pattern; generalize ringBell k=v; induction v using Finsupp.induction_linear with
  | zero=> simp
  | add _ _ hi hj=> simp only [map_add,embDomain_add,hi,hj]
  | single i c=> simp [glyph]

-- hidden all degree mass bounds from polynomial λ on fixed covariance. reuse Price.kv
section
variable {V V' : Type*}
omit [∀ i,AddCommGroup (R i)][∀ i,One (R i)] in
private lemma pay_glyphs (K: ∀ i:J,(Z→Four (R i))→JetGauge.Cov V) (h:∀ a b,Quotation (fun i z=>(K i z).cov a b))(u:V'→V) (a:Finset V'): Quotation (fun i z=> blend (K i z) 0 (Next.Rank.Normal.glyphs u a)) := by
  classical
  induction a using Finset.strongInduction with
  | H a ih=>
    by_cases p:a=∅; subst a; simp [Next.Rank.Normal.glyphs]; exact Quotation.const J Z 1
    obtain ⟨j,hj⟩:= Finset.nonempty_iff_ne_empty.mpr p
    rw [show a=insert j (a.erase j) from (Finset.insert_erase hj).symm]; simp_rw [spring _ _ _ _ (Finset.notMem_erase _ _),Pi.zero_apply,zero_mul,zero_add]; exact Quotation.sum _ _ (fun k _=> (h (u j) (u k)).mul (ih _ (Finset.ssubset_of_subset_of_ssubset (Finset.erase_subset ..) (Finset.erase_ssubset hj))))
omit [∀ i,AddCommGroup (R i)][∀ i,One (R i)] in
lemma uniform_glyph (K: ∀ i:J,(Z→Four (R i))→JetGauge.Cov V) (h:∀ a b,Quotation (fun i z=>(K i z).cov a b))(p:poly V): Quotation (fun i z=> blend (K i z) 0 p):=by
  classical
  suffices H : ∀ m c, Quotation (fun i z=> blend (K i z) 0 (monomial m c)) by rw [p.as_sum]; simp_rw [map_sum]; exact Quotation.sum _ _ (fun i _=> H ..)
  intro m c; let I:=(i : m.support) × Fin (m i.val); let a (x:I):=x.1.val
  have he: monomial m (R:=ℂ) c=c • glyphs a Finset.univ:=by rw [monomial_eq,← C_mul']; congr 1; simp [glyphs,I,a,Finsupp.prod,Fintype.prod_sigma]; apply Eq.symm; rw [Finset.prod_attach _ (fun i=> MvPolynomial.X (R:=ℂ) i ^ m i), monomial_eq,map_one,one_mul]; rfl
  rw [he]; simp_rw [map_smul]; exact (Quotation.const J Z c).mul (pay_glyphs K h a Finset.univ)
lemma estimate (h:Society F)(p: Shadow (Z:=Z) (G:=G)): Quotation (fun i z=>blend (F i).grant 0 (motor (F i) z p)):= by
  let K (i:J) (z:Z→Four (R i))(k:Z × Bone G ℤ): Bone G (R i) →₀ℂ:= single (jump (F i) z k) 1
  have hx i z : motor (F i) z= exchange (K i z):= labelled ..
  simp_rw [hx,wets, show ∀ i z,reads (K i z) 0=0 from fun i z=> by ext k; simp [reads]]; apply uniform_glyph; intro a b
  obtain ⟨C,hC,H⟩:= h.every; exact ⟨C,hC,fun i z=> by dsimp only [K]; rw [match_name (jump (F i) z)]; apply H⟩
end
end YM.XSpace.Outline
