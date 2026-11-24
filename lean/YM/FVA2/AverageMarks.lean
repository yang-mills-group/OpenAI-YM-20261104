import YM.FVA2.TuningBind
/-!
# Averaging the momentum proof, not a norm estimate on the field conversion

Covariance and unit lift on MS_data are statements on entire four-dimensional
momentum kernels. Assumed of arbitrary comparison fields here; construction
and unit condition are SEPARATE. Choose proposition not a dependent record
on witness, so constructions suffice.
-/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 900000
set_option maxRecDepth 10000
namespace YM.FVA2.Blaze
open Lattice MS MS.Local.Physical MS.Menus MS.SpinCode MS.Plane MS.City MS.Wind.Leading
open ColorCode Plate Filter Topology Set Function MeasureTheory PertExtension
open Wilson MS.Native MS.Native.Wilsonian MS.Lifting MS.Landau MS.Landau.Detect MS.Koszul MS.Book MS.Book.Program
open MS.Cylinder MS.Cylinder.Lab MS.Book.Convolve MS.Tone MS.Color MS.Logarithm MS.High MS.High.Knobs MS.Wind MS.Land
open MS.Pearl MS.Train MS.Outlook MS.Mach
open scoped Topology Classical ContDiff
variable {G:Gauge} (s:Signed) (TQ: Warehouse G)
local notation "Γ"=> TQ.F
local notation "B"=> wings G
local notation "V"=> TQ.native (wings G)
variable {M:Booked (wings G)} (A:MS_Data G M) (P: Prescription (wings G)) {d:ℕ}
-- orient equation shape. Real/nested degree. prove by DR construction elsewhere.
abbrev displayD (d:ℕ)(i: Land.Plaid (wings G) d) := Archive d ( A.marks d i )
abbrev Ω (d:ℕ) (i:Plaid (wings G) d) := P.fees d i
variable (i j:Plaid (wings G) d) (t:Team)
-- avoiding unguarded free macro
structure Turns (TQ:Warehouse G) {M:Booked (wings G)} (A:MS_Data G M):Prop where
   turns (s:Signed) (d:ℕ) (i:Plaid (wings G) d) : (flipScore s ( displayD A d i ))= ∑ j:Plaid (wings G) d,(( ColorCode.fee TQ.F s.ortho d i j :ℝ):ℂ) • displayD A d j

private lemma col_sumM {X:Type}{Z:Local.Physical.Deck G}(XX: BookM Z)(p:X→Acts Z d)(S:Finset X)(f:X→ℝ): col (horizonM XX t (fuse S p f))=∑ i∈S, (f i:ℂ) • col (horizonM XX t (p i)):= by rw [horizon_f]; funext n x; simp_rw [ Finset.sum_apply,Pi.smul_apply,col,Finset.sum_apply,Pi.smul_apply]
private lemma col_scaledM (X:Acts (wings G) d): col (horizonM V t (castA TQ X s))= flipScore s (col (horizonM V t X)):= by rw [step_cast]; rfl
-- average over all Sym t inverse-input transform. Include weights **preceding proof**, they may cost higher Budgets.
private lemma wmono (s:Ortho) (i j:BasisIx G d)(h:i.grade≠j.grade): shows Γ s d i j=0:= by rw [shows,shown_off]; rfl; exact fun t=> h (congr_arg Prod.snd t)
lemma read_inj : Function.Injective (@YM.MS.Land.read G d (wings G)):= by
   intro i j h; apply eq_of_heq; exact (Sigma.mk.inj h).2
private lemma fee_one (i j: Plaid (wings G) d) : ColorCode.fee Γ 1 d i j= if i=j then 1 else 0:= by
   unfold ColorCode.fee shows; rw [white_count]; by_cases h:i=j; simp [h]; rw [if_neg h,if_neg (fun e=>h (read_inj e))]; rfl -- order
private lemma fe_inv (p:Signed)(i j:Plaid (wings G) d) : (∑ x:Plaid B d, ColorCode.fee Γ p⁻¹.ortho d i x*ColorCode.fee Γ p.ortho d x j)= if i=j then 1 else 0 := by rw [← fare_l,show p.ortho*p⁻¹.ortho=1 from (by simp only [show p⁻¹.ortho=p.ortho⁻¹ from Signed.inclusionO.map_inv _, mul_inv_cancel]),fee_one]

abbrev listW (i:Plaid (wings G) d) : Finset ( Plaid (wings G) d ):= Finset.univ.filter fun j=> (Land.read i).grade=(Land.read j).grade
def waveP (s:Signed)(i:Plaid (wings G) d) : Acts (wings G) d:= fuse (listW i) (fun j=> castA TQ (P.fees d j) s) (fun j=> ColorCode.fee TQ.F s⁻¹.ortho d i j)
private lemma summa {X:Type*}[AddCommMonoid X] (f:Plaid (wings G) d→X)(h:∀ j: Plaid B d,j∉listW i→ f j=0): ∑ j∈ listW i,f j=∑ j: Plaid B d,f j:= Finset.sum_subset (Finset.subset_univ _) (fun j _ hj=>h j hj)
private lemma fee_off (i j:Plaid (wings G) d) (p:Ortho)(h:j∉listW i): ColorCode.fee Γ p d i j=0:= wmono TQ p _ _ (by simpa [listW] using! h)
lemma seesP (k:ℕ)(x:BasisIx G d) (i:Plaid (wings G) d): (waveP TQ P s i k).register x= ∑ u:Plaid (wings G) d, ColorCode.fee Γ s⁻¹.ortho d i u • (∑ j:BasisIx G d,shows Γ s.ortho d j x • ( P.fees d u k ).register j):= by unfold waveP; rw [register_fuse]; apply summa; intro j h; rw [fee_off TQ _ _ _ h,zero_smul]
lemma wave_start (i:Plaid (wings G) d) : FitOrder (Land.read i) (waveP TQ P s i 0) where
   Low x:= by
      unfold waveP; apply low_fuse; intro j h z; have hp : (Land.read i).grade=(Land.read j).grade:= Finset.mem_filter.mp h|>.2; rw [hp]; exact ceiling s ((P.init d j).Low z) -- maybe namespace
   Single x h:= by
      -- use FILTERED formula; for j in ListW leading known, get unit. then extend to full
      unfold waveP; rw [register_fuse]; have hc (j:Plaid B d)(hj:j∈listW i): ((castA TQ (P.fees d j) s) 0).register x= Polynomial.C (shows Γ s.ortho d (Land.read j) x) := by
          let u:= P.fees d j; let r:= Land.read j; change ∑ k:BasisIx G d,shows Γ s.ortho d k x • ( u 0 ).register k= _; rw [Finset.sum_eq_single_of_mem r (Finset.mem_univ _ )];
          · rw [(P.init d j).Single r (le_refl _),if_pos rfl, Polynomial.smul_eq_C_mul,mul_one];
          intro k _ hk; by_cases hm:k.grade=x.grade; · have he := Finset.mem_filter.mp hj|>.2; rw [ (P.init d j).Single k (by omega), if_neg hk,smul_zero ];
          rw [ wmono TQ _ k _ hm, zero_smul ]
      rw [Finset.sum_congr rfl (fun j hj=>congr_arg ( ColorCode.fee Γ s⁻¹.ortho d i j • · ) (hc j hj)), summa i ]; swap; · intro j hj; rw [fee_off TQ _ j _ hj,zero_smul]
      by_cases hy: x.size=d; · obtain ⟨u,rfl⟩:= owner_exists d x hy; simp_rw [ Polynomial.smul_eq_C_mul, ← map_mul, ← map_sum ];
                                change Polynomial.C (∑ j:Plaid B d, ColorCode.fee Γ s⁻¹.ortho d i j * ColorCode.fee Γ s.ortho d j u)=_; rw [fe_inv ]; by_cases h:i=u; simp [h]; rw [if_neg h, if_neg (fun e=> h (read_inj e.symm))]; exact map_zero _
      rw [if_neg (fun h=>hy (congr_arg Glyph.size h))]; exact Finset.sum_eq_zero fun j _=> by rw [shows, shown_off TQ.F s.ortho d (Land.read j) x (fun h=> hy ((congr_arg Prod.fst h).symm))]; simp
def vision : Prescription (wings G) where
    team:= P.team
    fees d i:= fuse (Finset.univ:Finset Signed) (fun s=> waveP TQ P s i) (fun _=> (↑(Fintype.card Signed):ℝ)⁻¹)
    init d i:= by
       refine ⟨low_fuse _ _ _ _ (fun j _=> (wave_start j TQ P _|>.Low)),fun j h=>?_ ⟩; rw [register_fuse]; simp_rw [ ( wave_start _ TQ P i ).Single j h ]; rw [ ← Finset.sum_smul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ (by positivity), one_smul ]
lemma together (H:Turns TQ A)(h:TaylorOKM A (TQ.native (wings G)) P) : TaylorOKM A (TQ.native (wings G)) (vision TQ P) := by
   refine ⟨ h.bulk, fun d i=> ?_⟩; let P':= vision TQ P; let x:= displayD A d i; let p:= P.team; let Q := V;
   have he (s:Signed) : Fixed (col (horizonM V p (waveP TQ P s i))) x false d 0:= by
       unfold waveP; rw [col_sumM]; simp_rw [col_scaledM];
       have hu: x= ∑ j∈listW i,(↑(ColorCode.fee Γ s⁻¹.ortho d i j):ℂ) • flipScore s ( displayD A d j ):= by
          conv_rhs=> rw [summa i _ (fun j hj=>by rw [ fee_off TQ _ _ _ hj,Complex.ofReal_zero,zero_smul]) ]; -- expand
          funext n v; change displayD A d i n v= _
          -- h.turns at s^-1 suffice
          obtain hv := congr_fun (congr_fun ( H.turns s⁻¹ d i ) n ) v;
          change backlit (s⁻¹)⁻¹ (displayD A d i n v)= _ at hv; rw [inv_inv] at hv
          rw [← shift_back s (displayD A d i n v), hv]; simp only [ Finset.sum_apply, map_sum,Pi.smul_apply,map_smul ]; rfl
       rw [ hu]; apply narration; intro j _; exact presses (winds _ (h.mark _ j)) _
   let c:ℝ:= (↑(Fintype.card Signed):ℝ)⁻¹; unfold vision; change Fixed ( col _ ) x false d 0; rw [col_sumM ]
   have hx : ∑ _i:Signed,(c:ℂ) • x=x:=by rw [← Finset.sum_smul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; dsimp only [c]; push_cast; rw [mul_inv_cancel₀ (by exact_mod_cast Fintype.card_pos (α:=Signed) |>.ne'),one_smul]
   rw [ ← hx ]; exact narration Finset.univ (fun i _=> presses ( he i ) (c:ℂ))

open Pert.Position
local notation "Ψ"=> (sameAxis Γ d)
def factory {T:Warehouse G}{d:ℕ}(V':Glyph (wings G) d→ℂ): E (T.F) d:= ∑ i, V' i • sameAxis T.F d i
-- required exact rotation commute restated on mark-output native *coefficient vector*; holds before dimension weights. Use to preserve filtration too.
structure ExactSpin (T:Warehouse G) (P:Prescription (wings G)): Prop where
   legal (s:Signed) (d:ℕ) (j:Plaid (wings G) d) (x:ℝ)(n:ℕ) :
         spin T.F s.ortho d (factory (T:=T) (fun i=> oil (P.fees d j) i n x))=
             ∑ k:Plaid (wings G) d, ColorCode.fee T.F s.ortho d j k • factory (T:= T) (fun i=>oil (P.fees d k) i n x)
local notation "ℰ"=> factory (T:=TQ)
abbrev sketch (V':Prescription (wings G)) (d:ℕ)(x:ℝ)(n:ℕ)(u:Plaid (wings G) d):= factory (T:=TQ) (fun i=> Menus.oil ( V'.fees d u ) i n x)
private lemma at_total {I:Type} (S: Finset I) (V': I→ Acts (wings G) d)(f:I→ℝ)(x:ℝ)(n:ℕ):
    ℰ ( fun i=> oil (fuse S V' f) i n x )=∑ i∈S,(f i:ℂ) • ℰ (fun j=> oil (V' i) j n x):= by
   unfold factory; simp_rw [oil_f, Finset.smul_sum, Finset.sum_smul, mul_smul]; rw [Finset.sum_comm]
private lemma at_spin (X:Acts (wings G) d)(x:ℝ)(n:ℕ): ℰ (fun i=> oil (castA TQ X s) i n x)=spin Γ s.ortho d (ℰ (fun j=>oil X j n x)):= by
   unfold factory; simp_rw [oil_cast,map_sum,map_smul,show ∀ i:BasisIx G d,spin Γ s.ortho d (sameAxis Γ d i)=_ from fun i=> displays Γ s.ortho d i, Finset.sum_smul,Finset.smul_sum, mul_smul,held_real, smul_comm (showsC _ _ _ _ _) (oil _ _ _ _) ]; rw [Finset.sum_comm]
-- turn the map under conjugation (inverse on input, forward on output)
private lemma rebuild (x:ℝ)(n:ℕ)(p:Signed)(j:Plaid (wings G) d) :
  ℰ (fun i=> Menus.oil (waveP TQ P p j) i n x)= ∑ i:Plaid B d,( ColorCode.fee Γ p⁻¹.ortho d j i:ℂ) • ColorCode.spin Γ p.ortho d (sketch TQ P d x n i):= by unfold waveP; rw [ at_total ]; simp_rw [at_spin]; apply summa; intro i hi; rw [fee_off TQ _ _ _ hi, Complex.ofReal_zero,zero_smul]
private lemma earth (p u:Signed)(x:E TQ.F d) : spin Γ p.ortho d (spin Γ u.ortho d x)=spin Γ (p*u).ortho d x:= by apply PositionX.physical_inj; simp only [spin,Pert.RawLabels.physical_ortho TQ.F,show (p*u).ortho=p.ortho*u.ortho from map_mul Signed.inclusionO p u, Labels.tensor_mul]
lemma vision_angular : ExactSpin TQ (vision TQ P) := by
  constructor; intro s d j x n; let Tφ (p:Signed):= spin Γ p.ortho d -- replaces notation
  let Δ := sketch TQ P d x n; let L:= (↑(Fintype.card Signed):ℂ)⁻¹
  let f (k:Plaid (wings G) d) (t:Signed):= ℰ (fun i=> Menus.oil (waveP TQ P t k) i n x)
  have he t: Tφ s (f j t)=∑ q:Plaid B d,( ColorCode.fee Γ s.ortho d j q:ℂ ) • f q (s*t):= by
     -- matrix incidence contraction
     unfold f; simp_rw [rebuild]; rw [map_sum]; simp_rw [map_smul, Tφ, earth TQ s t, Finset.smul_sum ]; rw [Finset.sum_comm];
     apply Finset.sum_congr rfl; intro i hi; simp_rw [smul_smul, ← Complex.ofReal_mul,← Finset.sum_smul, ← Complex.ofReal_sum, ← fare_l]; congr 3; change Signed.inclusionO _= Signed.inclusionO _* Signed.inclusionO _; simp
  have hh (i:Plaid B d) : sketch TQ (vision TQ P) d x n i=∑ k:Signed,L • f i k:= by unfold vision sketch f;rw [at_total]; simp [L]
  change Tφ s (sketch TQ (vision TQ P) d x n j)=∑ i:Plaid B d, ColorCode.fee Γ s.ortho d j i • sketch TQ (vision TQ P) d x n i
  rw [hh,map_sum]; simp_rw [map_smul,he,Finset.smul_sum]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _=>?_ ; simp_rw [ smul_comm L ( ↑(ColorCode.fee Γ s.ortho d j i):ℂ ), ← Finset.smul_sum ]; rw [ hh, ← Finset.smul_sum, show ∑ k:Signed,f i (s*k) = _ from Equiv.sum_comp (Equiv.mulLeft s) (f i) ]; exact Eq.symm (RCLike.real_smul_eq_coe_smul (K:=ℂ) ..)
end YM.FVA2.Blaze
