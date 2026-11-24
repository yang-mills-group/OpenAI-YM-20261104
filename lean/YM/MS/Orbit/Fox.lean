import YM.MS.Orbit.Seq
/-!
# Fuse ext B&D; path half. No invariant-bare assumptions from known Ψ yet.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Orbit.LogReal
open Set Function Filter Finset Metric MeasureTheory
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Snap Native Lattice City Latch Job Belt Flux Cog Wire Rake Book Convolve
open scoped Topology ContDiff Interval
variable {G:Gauge}{A E W I:Type}{L:I→Side}{K:Planet G I}{X:Rake.Site G I}{b:Bool}{ T:H_defect G I}{n:ℕ}{Y:ℕ→I→Law G}
variable (i:I)
abbrev C_wind (K:Planet G I)(Z:Lin I)(X:Rake.Site G I)(i:ℕ):= CPlan Z K ( X i )+ ( (2:ℂ)⁻¹) • groups K X X i
abbrev ΦD (K:Planet G I)(Z:Lin I)(X:Rake.Site G I)(T:H_defect G I)(i:ℕ)(z:Half):= zip0 Z K (loci Z z) (T z i) + HCur Z K X T i z
abbrev Valve (L:I→Side)(b:Bool)(X:Rake.Site G I)(D:H_defect G I)(i:I):= Panels L b i X+states L b D i
local notation "Γ"=> σbranch (G:=G) (n:=dimT L i)
local notation "Ω"=> enterV L b
local notation "Ψ"=> zoneP L b K i
variable (h:Glow K)(he: ∀ n,Knits (X n)) (hp: ∀ x n, Knits ( T x n )) (hm:∀ n,StandGuard L ( X n ) i)
abbrev ωr:= ((2:ℂ)⁻¹)
omit i in
lemma S_static {L:Lines A}[Fintype A] {T P:OM A} : Static L (T+P)=Static L T+Static L P := by ext i; exact congr_fun (map_add (Cog.frame ( L i )) ( T i ) ( P i )) _
omit i in
lemma S_sum {L:Lines A} [Fintype A](K:E→OM A)(S:Finset E): Static L (∑ i∈ S,K i)=∑ i∈ S, Static L (K i) := by classical induction S using Finset.induction with| empty=> simp only [Finset.sum_empty]; funext t; exact map_zero (Cog.frame ( L t ))| insert i s hi ih=>rw [ Finset.sum_insert hi,S_static,ih,Finset.sum_insert hi ]
include h he hp hm
lemma level_Θ (hz:0<n): Level Γ Ψ ( Valve L b X T i ) ( Valve L b X T i ) n 1= PayB L b i (groups K X X n) + ( ∑ q: Half, PayA L b i (loci Ω q) ( (2:ℂ) • groups K X ( T q ) n + foam Ω K T ( T q ) (loci Ω q) n 1 )) := by
   let R:= rung Ψ Γ n 1; let X':=Panels L b i X; let T':=states L b T i; have hx:R T' X'=R X' T':= counterpart hz (fun u q=> swap_net h ( T' u ) ( hm q )); change R (X'+T') (X'+T')= _; rw [map_add R,LinearMap.add_apply,map_add,map_add,hx];
   have ht:R X' T'=∑ q:Half, PayA L b i (loci Ω q) (groups K X ( T q ) n):= by unfold T' states; rw [ map_sum ]; exact Finset.sum_congr rfl fun j _=> level_ba (i:=i) h he hm (hp j) n 1
   have hu:R T' T'= ∑ q:Half, PayA L b i (loci Ω q) (foam Ω K T (T q) (loci Ω q) n 1):= by rw [show R T' T'= R T' ( ∑ q:Half, Helm L b i T q) from rfl, map_sum ]; exact Finset.sum_congr rfl fun j _=> level_d (i:=i) h (hp j) n 1
   rw [ht,hu,show R X' X'=_ from level_b (i:=i) h he hm ( b:=b ) n 1 ]; simp_rw [ map_add,map_smul,two_smul, Finset.sum_add_distrib ]; abel
lemma billing (hz:0<n): Static Ψ ( Valve L b X T i n )+ωr • (Level Γ Ψ ( Valve L b X T i ) ( Valve L b X T i ) n 1)= PayB L b i ( C_wind K Ω X n ) + ∑ q:Half, PayA L b i ( loci Ω q ) ( ΦD K Ω X T n q ):= by
   rw [ level_Θ i h he hp hm hz ]; let c:=ωr; rw [smul_add, Finset.smul_sum, show Valve L b X T i n= PayB L b i (X n)+∑ q:Half, PayA L b i (loci Ω q) ( T q n ) from ?p, S_static,pay_cycleB (L:=L) b (he n|>.1) h,S_sum ]; -- signature
   simp_rw [ show ∀ q:Half,Static Ψ ( PayA L b i (loci Ω q) ( T q n ))=_ from fun q=> pay_cycleA b L i ( hp q n|>.1 ) h ]; simp_rw [ map_add,map_smul, smul_add, smul_smul,show ωr * 2=1 from (by norm_num [ωr]) ]; -- rhs hidden abbreviations.
   unfold HCur RotateX ωr; simp_rw [one_smul, map_add,map_smul, Finset.sum_add_distrib]; abel
   case p=> unfold Valve Panels states; rw [Pi.add_apply,Finset.sum_apply]; rfl
-- initial B.Pay Reader.P.Assign.
def B_init (G:Gauge)(L:I→Side)(b: Bool)(Y:ℕ→I→Law G)(i:I): SpecB (FixedMode G (dimT L i)):= fun j=> Scan b L i ( Y j i )
lemma dictates (hB: Script Ω K Y X)(hV: RecipeD Ω K X T): Background Γ Ψ ( B_init G L b Y i ) ( Valve L b X T i ):= by
   constructor
   · unfold Valve Panels states; rw [ Pi.add_apply, Function.comp_apply, hB.1,map_zero, zero_add, Finset.sum_apply]; exact Finset.sum_eq_zero fun j _=> by unfold Helm Ag; rw [Function.comp_apply,(hV j).1,map_zero]
   intro n hn; refine ⟨?_,?_⟩
   · unfold Valve Panels states; rw [Pi.add_apply,Pi.add_apply,Finset.sum_apply,Finset.sum_apply]; rw [ Finset.sum_eq_zero (fun j _=> ?_) ]; simp only [add_zero,Function.comp_apply,pay_at,( hB.2 n hn ).1 i]; rw [ B_init,Vexp ];
     change Aspect b L i (loci Ω _) ( T j n i 0)= _; rw [(hV j|>.2 n hn).1 i,Pi.zero_apply,map_zero]
   rw [ billing i h he hp hm hn ];  apply status_plus ( F:=Panels L b i X n ) (glpto (P:=Scan b L i) ( GlB b L i ) ( prop_status ((hB.2 n hn).2) i )); unfold states; rw [Finset.sum_apply]; exact status_sum _ (fun j _=> glpto (P:=Aspect b L i (loci Ω j)) ( GlA b L i ( loci Ω j )) (prop_status ((hV j).2 n hn|>.2) i)) -- names order statuses
end YM.MS.Orbit.LogReal
