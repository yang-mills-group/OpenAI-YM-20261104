import YM.FVAAlt2.Turn.Still
import YM.FVAAlt2.Convert.Comply
/-! Assemble, certify `Launch` without any rent positivity hypothesis (detector
 funding remains a distinct task -- this stage gives just normalized field numbers
 in real position geometry of the SAME Fields system). -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Convert
open Function Finset Filter MeasureTheory Lattice
open MS MS.Koszul MS.Menus MS.Local.Physical MS.Land MS.FVA MS.FVA.Motions MS.FVA.Town MS.Lifting MS.Plane MS.Landau MS.Landau.Detect MS.Native MS.Theater
open FormalOPE FormalOPE.RG10 Labels Source Home
open MS.Mach MS.Wind MS.High MS.High.Knobs MS.Hem.Mell MS.Outlook
open MS.Book MS.Book.Program MS.Logarithm
open MS.Cylinder MS.Cylinder.Taylor MS.Cylinder.Lab MS.Native.Draft
open PertExtension PertExtension.LatticePT PertExtension.Orb PertExtension.Orb.SlotEvaluation
open scoped Topology BigOperators ContDiff PowerSeries Classical Matrix
variable {G:Gauge} {F:Frames G} {B:Deck G} {d m:ℕ} {c:ℝ}{t:ℤ} {p: Law G}
variable (P:Position.Plan F)
local notation "Y"=> seats P.liftOff P.certified
local notation "R"=> Lobby.Table (Profiles.nativeR P) Y

local notation "Cz"=> piece (A:=LightMode G Cover) (1:ℂ)
variable {T:Labels.Frame G 0}
variable {H:Hol G}(S:SectionData T)(h:S.Sound H) (hx:Bid.pop S)
include h
lemma seal_o : Shop.origin S 0=Cz := by
 refine ( enterEq .. ).mp ( Eventually.of_forall (fun n=> ?_) ); rw [Shop.doc_co, unit_zero h]; change Taylor.ink _ (fun _=>1)= (Ferry _ Cz).val; rw [ coin_settled, ink_const ]; simp; rfl
include hx
lemma unit_menuM (i:Plaid B 0): ∃ b:ℂ, Shop.RBook B S h hx i.2=b • gold G:=by
 obtain ⟨b,hb⟩:= scalar_grade 0 (show Shop.seat (d:=0) B i.2∈ Grade (0,0) from by exact (congr_arg (fun k:ℕ=> Shop.seat (d:=0) B i.2 ∈ Grade (0,k)) ( show i.1.val=0 from le_antisymm (Glyph.memory (Land.read i)) (Nat.zero_le _))) ▸ Shop.isSeated B i.2); refine ⟨b,?_⟩
 let f(j:T.Index):=T.e0 j; unfold Shop.RBook; have hx0 (j:T.Index): Shop.valueP B S h hx i.2 j = if j=0 then b else 0:= by unfold Shop.valueP Shop.purchase; rw [hb, map_smul, T.coords_unit]; simp [Pi.single_apply,Frame.e0, ite_mul, topBasis_unit S H h hx]; split_ifs <;> simp -- args & if
 simp_rw [hx0,ite_smul,zero_smul]; rw [Finset.sum_ite_eq', if_pos (mem_univ _)]; refine congr_arg (b • ·) (funext fun n=>?_ ); unfold Shop.priceS; rw [T.zero_degree, seal_o S h]; exact gold_l ..
omit h hx
lemma start : Genesis R:= by
 let S:= P.source 0; have he:=P.sound 0; let h:=P.chosen 0; intro i c hu; obtain ⟨b,hb⟩:= unit_menuM S he h i; change (R).menu _ _ _ = _ at hb
 have ht := (R).rich 0 _ i.2 |>.ono; change (Land.read i).read = _ at hu; have hg:i.1.val=0:=le_antisymm (Glyph.memory (Land.read i)) (Nat.zero_le _)
 have hx := Fits.smul b (Fits.unit (G:=G) (b:=false)); specialize ht; rw [hb, show (Y).raw ((0:ℕ):ℕ) i.1.val i.2= _ from hu, Pi.smul_apply,gold, if_pos (Eq.refl 0), hg ] at ht
 suffices h:b=(c:ℂ) by rw [hb,h]
 have hv:= fit_determines hx ht; simpa [coin] using congr_fun hv []

variable (Z: RichBook B)
variable {V:Booked B}(X:MS_Data G V)
-- Launch general recipe. Feed geometry back. report fully explicit labels.
structure Launch (Ξ:Prescription B) : Prop where
 money:Spect F V
 high:TaylorOKPl X Z Ξ
 rent (n:ℕ): Permit F (Ξ.fees n)
 unit (i:Plaid B 0) (n:ℕ)(h:0<n) : ∀ j:Glyph B 0,(Ξ.fees 0 i n).register j=0
open Leading
set_option maxRecDepth 4200 in
lemma build_L (g:G.Simple) (hk:Genesis Z) (he: Spect F V)(hz:∀ s:Signed,∀ (t: Team) n, formsH Z t s (stepR F B n s)) : ∃ Ξ:Prescription B,Launch Z X (F:=F) Ξ:=by -- order check
 obtain ⟨ Ψ,hΨ ⟩:= High_stopsPl g X Z; let F₀ : (d:ℕ)→ Plaid B d→Acts B d:=fun d=>match d with|0=> rentFree B|n+1=> Ψ.fees (n+1); have ht(d:ℕ): firstOrder ( F₀ d ):= by cases d with|zero=>exact placid|succ d=> exact Ψ.init _
 let Q : Prescription B:= ⟨ Ψ.team, fun d=>net_A F (F₀ d), fun d=>bill₀ F (F₀ d) (ht d)⟩; refine ⟨ Q,he,{ bulk:=hΨ.bulk, mark:=fun i v=>?_},fun n=>permitted F (F₀ n), ?_⟩
 · refine net_gain Z (F₀ i) Ψ.team (fun s=> hz s _ _) X ?_ he v; intro j; cases i with| zero=> exact markTOP X hk Ψ.team j| succ i=> exact hΨ.mark _ j
 intro i n h₁ j; change (net_A F ( rentFree B ) i n).register j=0; simp_rw [net_A,swiv,venture,drives,rentFree,if_neg (by omega:n≠0)]; simp [show ∀ i:Glyph B 0,(0:Tact B 0).register i=0 from fun _=>rfl] -- inference.One

end YM.FVAAlt2.Convert
