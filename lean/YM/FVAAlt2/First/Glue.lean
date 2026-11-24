import YM.FVAAlt2.First.Impress
/-!
# d≤6 orientation at Fund + first identity criterion
Give credit for finite tests through order m only (m=1 used here). Danger reinterpreting any-arbitrarily order from same donor. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.First.Portray
open Function Set Filter Finset Topology Lattice MeasureTheory
open Precision Extra.FD Maxwell Labels Extraction Matrix
open FormalOPE FormalOPE.RG10.Gazebo FormalOPE.RG10.Position FormalOPE.RG10.Carryon
open Pert Pert.Position PertExtension PertExtension.LatticePT PertExtension.Position PertExtension.Position.Triangle PertExtension.Physical
open Home Home.Subsidy Tent SchemeConversionRG11
open RG10 (Through)
open PowerSeries (C coeff constantCoeff)
open scoped BigOperators Classical Topology PowerSeries Matrix
variable {G:Gauge}{F:Frames G}{m d n:ℕ}{q:Side}
local notation "V"=> RG10.Position.Deck F d
local notation "a0"=> PertExtension.Physical.Profile.n
local notation "K"=> deck F d
local notation "L"=> Maxwell.freeTable F
local notation "Ω"=> constantCoeff (R:=ℝ)
local notation "ZD"=> Datum V
local notation "J"=> ZD→fps
local notation "M"=> Matrix V V fps
local notation "ins"=> PertExtension.Position.insert (RG10.Position.Deck F d) PertExtension.Physical.Profile.n
variable {X : Stock F} (h:Official X)
abbrev freeX (F:Frames G)(d:ℕ):= RG10.Gazebo.raw F d
abbrev Debt (f:Datum ( RG10.Position.Deck F d )→fps)(m:ℕ) (b:ℕ→Datum ( RG10.Position.Deck F d )→fps): Prop:=∀ i:ZD,∀ j≤ m,Tendsto (fun t=> coeff j (b t i)) atTop (𝓝 (coeff j (f i)))
local notation "fQ"=> freeX F d
variable {A:Datum ( RG10.Position.Deck F d )→fps}{b:ℕ→Datum (RG10.Position.Deck F d)→fps}(he: ( PowerSeries.constantCoeff (R:=ℝ) ) ∘ A=freeX F d)
include h he in
lemma authority (v:Debt A m b): Debt ((X d).positioned A) m (fun i=>post X (b i)):= by
 let D:= X d; have hz:D.Regular (Ω ∘ A):= he ▸ h.fresh d; let w(i:ℕ)(j:ZD):= RG10.Carryon.up m (b i j) (A j)
 have ht (j:ZD): AlignSeries atTop (fun i=>w i j) (A j):= RG10.Carryon.aligning _ (fun i hi=> v j i (by simp at hi; omega))
 have H(i:ℕ): TestSystem.systemAt D A w i= crib X (w i):= congrArg (fun f:Datum V→ℝ=> D.leadingAdjust f (fun k=>Ω (w i k))) he
 intro z k hk
 apply (D.positions_align A w hz ht z k).congr; intro i; change coeff k ((D.systemAt A w i).positioned (w i) z)=_; rw [ H ]; exact ( posting (D:=X) (p:=w i) (q:=b i) (fun j _ t=> RG10.Carryon.copy m _ _) z.1 (fun t=> RG10.Carryon.copy m _ _) z.2 k hk ) -- named E likely D
variable (A b) {hq:1<q.val}{he: (PowerSeries.constantCoeff (R:=ℝ)) ∘ A= freeX F d}
include he in
lemma from_debt (H: Debt A m b): listens (D:=X) (l:=atTop) b:= by apply tendsto_pi_nhds.mpr; intro i; obtain h:=H (markIn (X d).tests i) 0 (Nat.zero_le _); have hv (i:ZD): coeff 0 (A i)=freeX F d i:= (PowerSeries.coeff_zero_eq_constantCoeff_apply _).trans (congr_fun he i); rw [hv] at h; simp_rw [ PowerSeries.coeff_zero_eq_constantCoeff_apply ] at h; exact h
include h
lemma revenue (he: Ω ∘ A=fQ) (Xt:ℕ→Matrix V V fps)(hx:∀ i,Upright (Xt i))(ht:∀ i,(Xt i).map Ω=(1: Matrix V V ℝ))(hd: Debt A m (fun t=> mix (b t) (Xt t))): Debt ((X d).positioned A) m (fun i=> post X (b i)):= by
 have hb: listens (D:=X) (l:=atTop) (fun t=> ins (b t) (Xt t)):= from_debt _ _ (he:=he) hd
 have hl:Tendsto (fun i=> Stg (Xt i) 0) atTop (𝓝 (1:Matrix V V ℝ)):= by simp_rw [show ∀ i, Stg (Xt i) 0=1 from fun i=> by rw [←ht i]; ext x y; simp [Stg]]; exact tendsto_const_nhds
 have hv := loading (b:=b) h Xt ( RG10.Carryon.forward hl hb ) hx hl hb; intro v k hk; refine (authority h he hd v k hk).congr' (hv.mono fun i hi=> congr_arg (fun f:Datum V→fps=> coeff k (f v)) hi)
-- Fund first.Triangle
omit h -- A b not in all subsequent
open MS.Land Convert
variable (q) (w:RG11.FirstW.Pack F) (Z:ℕ→RG11.FirstW.Pack F)
open RG11.FirstW
lemma amounts_loot : loot (Issue.bareSide (F:=F) (d:=d) q m)=plunge F m q d:=by funext i; ext1 k; unfold loot plunge; rw [PowerSeries.coeff_mk]; change _=coeff k (Home.Profiles.takeReal _); rw [ Home.Profiles.takeReal, PowerSeries.coeff_mk]; rfl
lemma pursued {w:ℕ→Issue F d}{k:Issue F d}(H:Issue.Limits m atTop w k) : Debt (loot k) m (loot ∘ w):=by
 intro v n hn; let lp := ContinuousMultilinearMap.apply ℝ (fun _ : Fin v.1.n=> E F d) ℂ (⇑(deck F d) ∘ v.snd); have hv := lp.continuous
 simp_rw [Function.comp_apply, loot, PowerSeries.coeff_mk ]; exact Complex.continuous_re.continuousAt.tendsto.comp ( hv.continuousAt.tendsto.comp (H v.1.n v.1.test n hn))
lemma seal0(Z:ℕ→Pack F)(k: Issue F 6)(hq:1<q.val)(H:Issue.Limits m atTop (FirstSap F q Z) k) (hk:m=0 ∨ k.Twist): Ω ∘ (loot k)=freeX F 6:=by
 -- can prove by tending.ZERO directly using Issue.FirstSap 0.
 funext v; let v0(i:ℕ):= loot (FirstSap F q Z i) v; have he(i:ℕ): constantCoeff (v0 i)= constantCoeff ( plunge F i q 6 v ):=by
    rw [ ← amounts_loot q ]; simp only [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; unfold v0 loot; simp_rw [ PowerSeries.coeff_mk, first0 ]
 have hx:= ( Home.Subsidy.start_cost q hq v )
 simp_rw [← he] at hx; change Ω (loot k v)=_; apply tendsto_nhds_unique _ hx; change Tendsto (fun i:ℕ=> Ω ( loot ( FirstSap F q Z i ) v )) atTop (𝓝 ( Ω (loot k v)))
 simp_rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact pursued H v 0 (Nat.zero_le _)

end YM.FVAAlt2.First.Portray
