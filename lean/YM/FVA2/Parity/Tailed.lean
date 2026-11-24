import YM.FVA2.Parity.Pole
/-!
# Propagate parity from initial marks to Archiving the pole computation

Uses the appropriate hypotheses in `MS_Data`, not assuming parity there.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Parity.Optic
open Function Set Filter Finset MeasureTheory
open MS MS.Plane MS.Momentum MS.Arts MS.Arts.Spin MS.Landau MS.Koszul MS.Heat
open MS.Book MS.Arc MS.Garment MS.Rock MS.Motif MS.Outlook MS.Plane.Wire MS.Alps
open MS.Rock.Path MS.Rock.Oceans MS.Plum MS.Hem MS.Hem.Mell MS.Dock MS.Train MS.Pearl MS.Halo
open _root_.YM.MS.Shine MS.Color Garment.Wave Garment.Wick Signal Book.Convolve
open Hue MS.Emit MS.Local.Physical MS.Menus MS.Land MS.Mach MS.Motif.Literal MS.Lifting MS.Arts.Pilot
open Position Position.Glazer
open Complex (I)
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{n m k v:ℕ}{w:ℤ}{H B:T ( Coat G )}{P X:T (Flats G)}
local notation "Ω"=>hue G
local notation "V"=> tints G
lemma program (t:ℕ): platform (fun i=> cycleP G i (P i)) k (fun i=> cycleP G (i+t) ( X i ))= cycleP G (k+t) ( platform P k X ):= by
    unfold platform; rw [ map_sum ]; apply Finset.sum_congr rfl; intro i hi; unfold cycleP; simp only [drive0,LinearMap.smul_apply, map_smul,smul_smul,Glazer.stem (cl_a G 0) ]; obtain he:= Finset.mem_antidiagonal.mp ( Finset.mem_filter.mp hi|>.1 ); rw [← he, add_assoc,Hue.sp i.1,mul_comm]
lemma horiz (a:T ( Coat G ))(t:ℕ)(h: comet m w P a X B): comet m w (fun i=>cycleP G i (P i)) (fun i=> sleeve G (i+t) (a i)) (fun i=> cycleP G (i+t) (X i)) (fun i=> sleeve G (i+t) (B i)) := by
    intro i; obtain ⟨⟨n,H,hV,hU⟩,-⟩:=h i; refine ⟨⟨n, Joint.via ( (Direct H).scale ( Hue.σ (i+t))) ?_, fun j=> ((clash hV) j).smul ( s_bk (i+t) ), ( Hue.top hU ).smul ( s_bk ( i+t) ) ⟩, False.elim ⟩
    rw [Parity.Optic.program]; simp only [map_add,cycleP,LinearMap.smul_apply,map_smul, smul_add]; exact common (fun _=>EventuallyEq.rfl) (pact_scaled (cycleH (clockMoon hV) (Knot.clearer (A_caps G 0))) _)
variable {Y: Deck G} {U: Booked Y}(A:MS_Data G U)(w:ℕ)(i:Plaid Y w)
lemma stand : (fun j=> sleeve G (j+i.1.val) ( A.poles w i j ))= A.poles w i∧∀ n,Pact (cycleP G (n+i.1.val) ( A.marks w i n )) (A.marks w i n):=by
    obtain ht:= A.markOK w i; obtain hz:= horiz _ i.1.val ht; simp_rw [ prepar ] at hz; exact unique_M hz ht ( spun A.bulkOK ).2
lemma archived (n:ℕ)(s t:ℝ): Hue.σ (n+i.1.val) • (Ω (hereZ w (A.marks w i n) s t))= hereZ w (A.marks w i n) s t:= by
    let P:= A.marks w i n; have hp:= live0 (s:=s) (y:=t) ((gang (A.markOK w i n)).dost); apply Shine.Lift.unique (f:= Parade P w t s); swap; exact hp
    apply Shine.Lift.congr (f:= Parade (cycleP G (n+i.1.val) P) w t s); swap; exact prom ( stand A w i|>.2 n ) _ _ _;
    rw [cycleP, LinearMap.smul_apply,page_smul,funext (Glazer.card P · w t s) ]; exact Shine.Lift.static (litS hp) _
theorem marks (n:ℕ)(c:ℝ×ℝ): Hue.only (n+i.1.val) (Archive w ( A.marks w i ) n c):= by rcases c with ⟨s,t⟩; exact ( only_id .. ).mpr ( congr_fun ( archived A w i n t s ) 0 )
end YM.FVA2.Parity.Optic
