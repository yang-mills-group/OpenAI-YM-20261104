import YM.FVA2.O.Enh.Sale
import YM.FVA2.Speed.Cells
/-!
# Upper estimates from the scale law of each system

On formal arrays (`teeth` pointwise with compact-uniform bounds). Includes
homogeneity of the leading correlation with exact engineering power. No estimates
on an actual nonperturbative theory involved.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Enh
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick Metric Real
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix
open FVA2.Scale MS.Rake MS.Theater Level O.Score LogTime MS.Plane MS.Heat MS.Tone Momentum Rake.Geo O.Seam
open Equator Facets
variable { G:Gauge }{ n m k : ℕ }{ K:Set ( Points n )}
variable {O: Booked ( Press.portDeck G ) }{M:MS_Data G O}{ν:ℝ}
variable {V: Arenas G}{R:ℝ→ Cn}{B:ℝ→ Frames G}{A:Album G}
abbrev Observed (A:Album G): Prop:=∀ (n:ℕ)(p:Scan G n)(k:ℕ), ContinuousOn (fun x=> coeff k ( A n x p )) (conf n)
lemma seenMS (ν:ℝ)(M: MS_Data G O): Observed ( install ( wave ν M )) := by
    intro n p k; exact ContinuousOn.congr ( (show ContinuousOn ( fun x=> Dframe.meteor ν M _ x k ( tape p (guardT p) ) ) (conf n) from fun i hi=> (Speed.Star.smooth_r ν M _ k i hi).continuousAt.continuousWithinAt ) ) ( fun i hi=> by rw [install,dif_pos hi, Reg.Point.story, coeff_mk ]; rfl ) -- Dframe ns
lemma pay_J (hp:IsCompact K)(he:K⊆conf n)(p:Scan G n)(hx:Observed A)(k:ℕ): Bounded_K ( fun i:↥K=>coeff k ( A _ i.val p ) ):= by obtain ⟨C,hC⟩:= hp.exists_bound_of_continuousOn (( hx _ p k ).mono he); exact ⟨ C,fun i=> hC i.val i.property⟩
namespace Uniform
-- inversion of time changes for both minimal and X if needed
variable (h:Law V R B)
local notation "Ω"=> install V
local notation "V'"=> replay
lemma flips {ϕ:ℝ→Score.Cast G}(H:Town ϕ): Town ( fun t:ℝ=> ϕ (-t)):=by
    intro i j k l; obtain he:= ( H i j k l ).pre (- ( Polynomial.X:Polynomial ℝ )); simpa only [ Polynomial.eval_neg,Polynomial.eval_X ] using he
include h
lemma teeth (he:Regular V)(hp:IsCompact K)(ht:K⊆conf n)(hv:Observed Ω) (p:Scan G n)(d:ℕ): ChargeP d (totalG p) (fun (i:↥K) t=> install V n ( squeeze (-t) ( i.val ) ) p):= by
    simp_rw [ Score.adjust_clock h he, neg_neg ]; refine ChargeP.grow ( ChargeP.joint ( a:=(totalG p:ℝ) ) feeV ?_ ) ( show (totalG p:ℝ) ≤ (totalG p:ℝ)+0 by simp ); unfold Score.marking concert; -- b0 inferred?
    apply ChargeP.sum; intro j _; refine ChargeP.times (ChargeP.extreme ( flips ( rhythm_b h ) ) _ _ ) ( ChargeP.Pact (fun l _=> Rain.cash ( pay_J hp ht _ hv l )) ?_ (fun _ _=> h.led _|>.start ) ); intro l hl; obtain hu:= ( FVA2.Scale.Rhythm.unit.mpr ( h.smooth l ) ).pre ( -( Polynomial.X:Polynomial ℝ ) ); exact Rain.rhythm ( f:=fun t=> coeff l ( R (-t) ) ) ( by simpa only [Polynomial.eval_neg, Polynomial.eval_X ] using hu )
lemma lead_l (t:ℝ)(p:Scan G n)(x:Points n): coeff 0 ( CoinQ t (install V) n x p)= coeff 0 ( install V n x p ):= by
    rw [ ← scale_l ]; by_cases hp:x∈ conf n; swap; · simp [ install,hp ]
    simp only [install, hp, ↓reduceDIte,Reg.Point.story,coeff_mk ]; let v:= totalG p; let X:= V v; let u:Stage n:=⟨ x,hp ⟩;
    have hv : actMark ( B t v ) (scaling t X)= couple ( R t ) X:= h.reads t v; let f:= tape p (guardT p); obtain he:= ( Dframe.Silver.status_lead ( t:=f ) ( B t v ) ( scaling t X n u ) ); rw [ ← show (actMark ( B t v ) (scaling t X)) n u 0 f=Dframe.status ( B t v ) _ 0 f from rfl,hv, couple, Program.pay0,( h.paid t v ).zero ] at he; exact he.symm
lemma lead_k (t:ℝ)(p:Scan G n)(x:Points n) : coeff 0 ( install V n ( squeeze t x ) p )= Score.fee (-t) ( totalG p )*coeff 0 ( install V n x p ):= by rw [← lead_l h t p x, CoinQ,coeff_C_mul,← mul_assoc,mul_comm ( Score.fee _ _ ) ( Score.fee _ _ ),fee_mul,one_mul ] -- rw wrong occurrence
lemma teeth_P (he:Regular V)(hp:IsCompact K)(ht:K⊆Outside n)(hv:Observed Ω)(p:Scan G n)(u:Q G)(d:ℕ) : ChargeP d ( (heft u:ℝ)+(totalG p:ℝ) ) (fun (i:↥K) t=> lonelyG Ω ( squeeze (-t) i.val ) u p):= by
    let S:= outgoing '' K; obtain he:= teeth h he ( K:=S ) ( hp.image ( continual continuous_const ( f:=fun (_:Points n)=> (0:Points 1)) ( g:=id ) continuous_id )) ( image_subset_iff.mpr ht ) hv ( Fin.append (Single u) p ) d; rw [ totalW,totalOne,Nat.cast_add ] at he; let hi: K→ S:= fun i=> ⟨ outgoing i.val, Set.mem_image_of_mem _ i.property ⟩; obtain hv:= ChargeP.pull he hi; unfold Function.comp hi at hv; simp_rw [ squeeze_home ] at hv; exact hv
end Uniform
end YM.FVA2.O.Enh
