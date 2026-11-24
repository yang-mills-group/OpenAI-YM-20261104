import YM.FVA2.RequireRank
import YM.FVA2.EvenToken
/-!
# Actual pricing has slot filter. Via constrained realization and uniqueness on compensation components.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Reed.Wax
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Wire Garment Color Book Convolve Signal Dock Rock Path Oceans
open Hem Mell Motif Literal Halo Alps Native Outlook High Detect Lifting Local.Physical
open Mach Train Pearl Emit Wind Wind.Leading Menus Program Knobs Native.Paint Native.Wilsonian Tone Momentum City Land
open scoped Topology ContDiff InnerProductSpace
variable {G:Gauge}{m n h d:ℕ}{p:Team}{B:Deck G} (y:ℝ)
variable (W:BookM B)(p:Team){P: Land.Booked B}(M: MS_Data G P)
-- rank sharp extension
structure Minted (P:Land.Prescription B) : Prop where
   rate (d:ℕ)(i:Plaid B d)(n:ℕ)(t:Glyph B d): ( Land.read i ).grade+n < t.grade → ( P.fees d i n ).register t=0
theorem drawing (h:G.Simple) (hq: Fixed (col (skyline G p)) ( Archive 4 M.bulk ) true 4 1) : ∃ P:Prescription B, TaylorOKM M W P ∧ Minted P ∧ P.team=p:= by
   choose V H1 H2 H3 using fun d (i: Plaid B d)=> Wax.headLock ( Land.read i ) W p (Archive 4 M.bulk) ( Archive d ( M.marks d i )) h hq ( Outlook.fieldD M.bulkOK (M.markOK d i) wisdom (( P.law d i).moodQ)) (initialHF (P.law d i) (sizeG i) (M.markOK d i)) (fun n x=> heightMark M i x n)
   exact ⟨ ⟨ p,V,H1⟩,⟨ hq,H2 ⟩, ⟨fun d i n=> ( H3 d i n ).1 ⟩,rfl ⟩ -- notation argument order
end YM.MS.Reed.Wax
namespace YM.FVA2.Erase
open Filter Topology Set Function MeasureTheory PertExtension
open Wilson Lattice MS MS.Menus MS.Native MS.Native.Chart MS.Native.Wilsonian MS.Native.Studio MS.Native.Paint
open MS.Native.Orient MS.Native.Sew MS.Native.Draft MS.Lifting MS.Landau MS.Landau.Detect MS.Koszul MS.Book MS.Book.Program
open MS.Pearl MS.Train MS.Outlook MS.Mach MS.Book.Convolve MS.Koszul
open MS.Plane MS.High MS.High.Knobs MS.City MS.Arc MS.Tone MS.Tone.Frame MS.Rock MS.Rock.Path MS.Land MS.Reed.Wax
open MS.Cylinder MS.Cylinder.Lab MS.Cylinder.Taylor MS.SpinCode ColorCode MS.Color MS.Plane.Wire MS.Plane.Flux
open Pert Pert.Position Lattice PertExtension.LatticePT PositionX PositionX.Bend BoxOffice
open MS.Logarithm Plate ArchTurn MS.Wind MS.Wind.Leading Blaze Frost Verne
open scoped Topology ContDiff Classical
variable {G:Gauge} (V: Warehouse G) {B: Booked (wings G)} (M:MS_Data G B) {p:ℝ}
variable (P: Prescription (wings G))(X:ExactSpin V P)(K: Trusted P)(T: Booth p V.F){h:G.Simple}
private lemma coin_mint : Minted P →Minted (vision V P):= by
   refine fun h=>⟨fun d i n j ht=>?_⟩; unfold vision; rw [ register_fuse ]; apply Finset.sum_eq_zero; intro s hs; rw [ waveP,register_fuse ]; have H:∑ u∈ listW i, ( ColorCode.fee V.F s⁻¹.ortho d i u :ℝ ) • ((castA V (P.fees d u) s n).register j)=0:= by
       apply Finset.sum_eq_zero; intro k hk; change _ • (∑ v:BasisIx G d,shows V.F s.ortho d v j • ( P.fees d k n ).register v )= _; have H:∑ v:BasisIx G d, shows V.F s.ortho d v j • ( P.fees d k n ).register v=0:= by
          apply Finset.sum_eq_zero; intro l hl; by_cases H:l.grade=j.grade; · rw [h.rate,smul_zero ]; obtain hh:= Finset.mem_filter.mp hk|>.2; omega
          rw [ shows, shown_off _ _ _ _ _ (fun he=> H (congr_arg Prod.snd he)),Complex.zero_re, zero_smul ]
       rw [H,smul_zero ]; -- λ ℚ
   rw [H, smul_zero ]
private lemma coinR (h: Minted P) : Minted (recover P):= by
    refine ⟨fun d i n j hp=>?_⟩; rcases d with _|d; · obtain he:= tip0 j; omega
    exact h.rate _ _ _ _ hp
set_option maxRecDepth 4000
include h in
private lemma s_all (p:Team)(H: Fixed (col (skyline G p)) ( Archive 4 M.bulk ) true 4 1)(hB: Blaze.Turns V M) : ∃ P:Prescription (wings G), Minted P ∧ TaylorOKM M (V.native (wings G)) P ∧ ExactSpin V P ∧ Trusted P ∧ P.team=p:= by
   obtain ⟨P,H,hV,F⟩:= drawing ( V.native (wings G) ) p M h H; refine ⟨ recover (vision V P ), coinR (vision V P) ( coin_mint V P hV ), pinOK V B M (vision V P) ?_, pinLegal V _ (vision_angular V P),⟨ fun _=>rfl ⟩,show P.team=p from F ⟩; exact together V M P hB H
-- exact price rule (Trusted adjustment), for all families actually pricing. This is uniform of order and clocks, Born.
variable {q:ℕ+} (hq:1<q.val)(Φ:Knocker h T q hq ( BoxOffice.warehouse V ))
include K X Φ
lemma reflected_meter (H:TaylorOKM M (V.native (wings G)) P) (hv:Blaze.Turns V M) : Minted P:= by
    obtain ⟨P',hv,hP,hx,hy,_⟩:= s_all V M (h:=h) P.team H.bulk hv; let hK:= MixedStory.ceases M V H h; let hJ:= MixedStory.ceases M V hP h; refine ⟨ fun d i n j hi=>?_ ⟩; rw [ prices_eq V M T P X K hK P' hx hy hJ hq Φ n d i j, hv.rate d i n j hi ]
-- package the two conditions for Laurent folks
lemma fare_pair (hv: Blaze.Turns V M)(H:TaylorOKM M ( V.native (wings G) ) P) (d n:ℕ)(i:Owner G d)(j:BasisIx G d)(hi:( P.fees d i n).register j≠0): ∃ v:ℕ,n+(Land.read i).grade=j.grade+2*v:= by
    have hx:= reflected_meter V M P X K T hq Φ H hv; have hh:j.grade ≤ n+(Land.read i).grade:= by by_contra hQ; exact hi ( hx.rate d i n j (by omega) ); -- orientation
    have hu:Even ( j.grade+(Land.read i).grade+n):= Nat.not_odd_iff_even.mp (fun h'=> hi (parity_rule V M T P X K (MixedStory.ceases M V H h) hq Φ j i h')); -- h conflict
    refine ⟨ ( n+(Land.read i).grade - j.grade ) / 2,?_⟩; obtain ⟨u,hu⟩:=hu; omega
end YM.FVA2.Erase
