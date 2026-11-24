import YM.FVAAlt2.Convert.Optics
import YM.FVAAlt2.Turn.Revenue
/-! Combine the explicit counterterms from High across signed rotations (not across
 space emplacements), with minimal hypotheses for pose equations. Optical fibers remain
 SAME UNDERLYING continuum data (Pact in DR acceptable).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Convert
open Function Finset Filter MeasureTheory Lattice
open MS MS.Koszul MS.Menus MS.Local.Physical MS.Land MS.FVA MS.FVA.Motions MS.FVA.Town MS.Lifting MS.Plane MS.Landau MS.Landau.Detect MS.Native MS.Theater
open FormalOPE FormalOPE.RG10 Labels Source Home Matrix
open MS.Mach MS.Wind MS.High MS.High.Knobs MS.Hem.Mell MS.Outlook
open MS.Book MS.Book.Program MS.Logarithm -- verify
open scoped Topology BigOperators ContDiff PowerSeries Classical Matrix
variable {G:Gauge} {F:Frames G} {B:Deck G} {d m:ℕ} {c:ℝ}{t:ℤ} {p: Law G}
variable (s:Signed) (W:Position.Plan F)
local notation "Y"=> seats W.liftOff W.certified
local notation "R"=> Lobby.Table (Profiles.nativeR W) Y
local notation "K"=> stepR F Y
local notation "N"=> stepR F B d
local notation "S"=> localStep F Y
local notation "D"=> Plaid Y
local notation "J"=> Glyph Y
local notation "cN"=> (Fintype.card Signed:ℂ)⁻¹
lemma whole_bill (i: J d) : Orient.pose s ∘ (R).menu _ _ i.2.2=∑ j:J d, ((K d s) i j:ℂ) • (R).menu _ _ j.2.2:= by
 have hn:= high i; let E:= i.size; have he : Orient.pose s ∘ _= _:= ribbon_l s W (d:=E) i.2; apply he.trans; let f:=fun j:J d=> ((K d s) i j:ℂ) • (R).menu _ _ j.2.2; let v(j:D E):= up (B:=Y) hn (Land.read j); have hu : Injective v:= fun _ _ ht=> eq_of_heq (Sigma.mk.inj (up_inj _ ht)).2; refine Eq.trans (b:= ∑ j:D E, f (v j) ) ?_ ?_
 · refine Finset.sum_congr rfl fun j _=>?_ ; unfold f; refine congr_arg₂ (· • ·) ?_ rfl
   unfold v; rw [movesOn]; have H:= climb_eq F s hn ( Land.read (B:=Y) i.2 ) ( Land.read j ); rw [show up hn (Land.read i.2)=i from Eq.symm (lampu i hn)] at H; exact H.symm -- wrong occurrence
 rw [← Finset.sum_image (f:=f) hu.injOn]; apply Finset.sum_subset (Finset.subset_univ _); intro j _ hj; unfold f; rw [ only_r F s _ _ (fun H=>?_) , Complex.ofReal_zero, zero_smul ]; obtain ⟨⟨j,h⟩,u⟩:=j; have he:j=E:= congr_arg Prod.fst H.symm; subst j; exact hj (mem_image.mpr ⟨ u,mem_univ _,rfl⟩)
lemma preamble_H (T:Team): formsH R T s (K d s):= by
 intro i x k; unfold Glyph.preamblePl; rw [ show Orient.pose _ _= Native.Wilsonian.wobble G T x (Orient.pose s ∘ (R).menu _ _ i.2.2) k from congr_fun (FVA.City.wob_train (s:=s) T x _) k ,whole_bill]; simp [map_sum,map_smul] -- watch parser & argument
variable (Q: D d→ Acts Y d) -- shadow sorts? d
set_option quotPrecheck false
local notation "Rloc"=> fun i j: D d=>(K d s) ( Land.read i ) ( Land.read j )
-- use any horizon.regular initially. Starlight certificates.Raw
abbrev roster (F:Frames G)(B:Deck G)(d:ℕ)(s:Signed) := (stepR F B d s).submatrix Land.read Land.read
lemma real_price (i j:Plaid B d) : (roster F B d s i j:ℂ)= localStep F B d s i j:= movesOn F s (Land.read i) (Land.read j)
variable (F) in
def swiv (Q:(Plaid B d)→ Acts B d)(v:(Plaid B d)): Acts B d:= venture univ (roster F B d s⁻¹ v) (fun j=> drives s (N s) (Q j)) -- notation declare
-- Cost messages
variable (ℜ:RichBook B)(Q:(Plaid B d)→ Acts B d)(T:Team)(a:∀ s, formsH ℜ T s (stepR F B d s))
include a
lemma cash_reach (i: (Plaid B d)) : Wind.col (horizonPl ℜ T (swiv F s Q i))= ∑ j: (Plaid B d),(localStep F B d s⁻¹) i j • pressX s (Wind.col (horizonPl ℜ T (Q j))) :=by
 unfold swiv; rw [bill_total]; simp_rw [bill_move ℜ T s _ _ (a s)]; funext n p; rcases p with ⟨x,y⟩; simp_rw [Wind.col, Finset.sum_apply,Pi.smul_apply]; apply Finset.sum_congr rfl; intro j _; rw [real_price]; rfl
variable {M:Booked (B)}(V:MS_Data G M)
abbrev leverM (i:(Plaid B d)):= Archive d ( V.marks d i )
-- Taylor property
theorem swivH (h:∀ i:(Plaid B d), MS.High.Knobs.Fixed (Wind.col (horizonPl ℜ T (Q i))) (Archive d (V.marks d i)) false d 0)(hM:Spect F M)(j:(Plaid B d)): MS.High.Knobs.Fixed ( Wind.col (horizonPl ℜ T (swiv F s Q j)) ) (Archive d (V.marks d j)) false d 0:= by
   have hh(k:(Plaid B d)) : ∑ i:(Plaid B d), (localStep F B d s⁻¹) k i • pressX s (Archive d (V.marks d i)) = Archive d (V.marks d k) := by
      simp_rw [ skyline_R s V hM, Finset.smul_sum,smul_smul ]; rw [ Finset.sum_comm ]; simp_rw [← Finset.sum_smul,← Matrix.mul_apply,Ξ_roll F B d s⁻¹ s,mul_inv_cancel,step_id F B d ]; simp [ Matrix.one_apply, ite_smul ]
   rw [cash_reach s ℜ _ T a,← hh j]; apply morning; exact fun i _=> morning_c (morningX _ ( h i )) _
-- squash and its combination identities
variable (F) in
def net_A (Q:(Plaid B d)→Acts B d)(j:Plaid B d): Acts B d:= venture univ (fun _:Signed=> (Fintype.card Signed:ℝ)⁻¹ ) (fun s=> swiv F s Q j)
omit a in
lemma annual (i:(Plaid B d)) : Wind.col (horizonPl ℜ T (net_A F Q i))=∑ s:Signed,cN • Wind.col (horizonPl ℜ T (swiv F s Q i)):=by
 unfold net_A; rw [bill_total]; funext n u; obtain ⟨y,t⟩:=u; simp_rw [ MS.Wind.col, Finset.sum_apply,Pi.smul_apply ]; push_cast; rfl
variable {s}
lemma net_gain (h:∀ i:(Plaid B d), MS.High.Knobs.Fixed (Wind.col (horizonPl ℜ T (Q i))) (Archive d (V.marks d i)) false d 0)(hM:Spect F M)(j: (Plaid B d)): MS.High.Knobs.Fixed ( Wind.col (horizonPl ℜ T (net_A F Q j))) (Archive d (V.marks d j)) false d 0:= by
 obtain he:= morning univ (fun s _=> morning_c (swivH s ℜ Q T a V h hM j) cN); rwa [← annual ℜ,Finset.sum_const,Finset.card_univ,← Nat.cast_smul_eq_nsmul ℂ, smul_smul,mul_comm (_:ℂ),living, one_smul] at he
end YM.FVAAlt2.Convert
