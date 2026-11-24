import YM.FVA2.DerivD.Staff
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.DerivD
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick Metric Real TopologicalSpace
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix ComplexOrder
open FVA2.Scale MS.Rake MS.Theater Level O.Score LogTime MS.Plane MS.Heat MS.Tone Momentum Rake.Geo
open Equator Facets Dframe O.Enh O.Bind O.Project
/-!
 # Finite constant-price expressions in coefficients. Helper for C^m estimates

 Work on real tangents. Prices are constant, not positions, may depend on mark
 and derivative order. Estimate may use different constants over different K,W.
 -/
variable {I J E F D:Type } [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup D][NormedSpace ℝ D]
variable {p:ℝ}
-- easier express list composition by existential arbitrary finite type & sum. Avoid Finset padding/use univ Fin.U
private lemma across {E F:Type} [NormedAddCommGroup E][NormedAddCommGroup F] {f:I→ℝ→E}{g:I→ℝ→F} (he:Rain p f)(ht:∀ᶠ t:ℝ in atTop,∀ i:I,‖g i t‖≤‖f i t‖): Rain p g:= by obtain ⟨C,hC,k,hV⟩:=he; exact ⟨ C,hC,k,( ht.and hV ).mono fun s hs i=> ( hs.1 i ).trans ( hs.2 i ) ⟩ -- Rain requires Normed..
omit [NormedSpace ℝ E][NormedSpace ℝ F] in
lemma throughF {f:I→ℝ→ E}(hx:Rain p f)(T:E→F)(u:ℝ)(hp:0≤u)(hT:∀ i,‖T i‖≤ u*‖i‖): Rain p (fun i t=> T (f i t)):= by
    obtain ⟨C,hC,k,h⟩:= hx; refine ⟨ u*C+1,(by positivity),k,?_⟩; filter_upwards [ h,eventually_ge_atTop ( 0:ℝ ) ] with t h ht i; apply ( hT _ ).trans; specialize h i; calc u*‖f i t‖ ≤ u*(C*post p t k):= (by gcongr)
                                                                                                                                        _ ≤ _:= (by rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (post_at ht).le; linarith)
-- pencil finite index expressions. add & precompose inert.Unit shape approach.
structure Pencil (I F:Type)[NormedAddCommGroup F][NormedSpace ℝ F] where
  site : Type
  finS: Fintype site
  send : site→ I
  mapS : site→ ℂ→L[ℝ] F
attribute [local instance] Pencil.finS
def Pencil.prime (P:Pencil I F)(f:I→ℂ):=∑ i:P.site, P.mapS i ( f ( P.send i ) )
-- proposition avoids universe max issues index Fin.W:exists finite type is Type1 okay
abbrev Stencil (P:(I→ℂ)→ F) : Prop := ∃ E:Pencil I F, P=E.prime
namespace Stencil
variable {P R:(I→ℂ)→F}
lemma only (T:ℂ→L[ℝ]F)(i:I): Stencil (fun f:I→ℂ=>T ( f i )):= by
    let p:Pencil I F:= ⟨ Unit,inferInstance,fun _=>i,fun _=> T ⟩; refine ⟨ p,?_ ⟩; funext f; unfold Pencil.prime; change _= (∑ _:Unit,T ( f i )); simp
lemma zero : Stencil (0:(I→ℂ)→ F):= by
    let P:Pencil I F:= ⟨ Empty,inferInstance, Empty.elim,Empty.elim⟩; refine ⟨ P,?_⟩; funext f; unfold Pencil.prime; apply ( Finset.sum_of_isEmpty _ ).symm -- inspect
lemma add (h: Stencil P)(hx: Stencil R): Stencil ( fun f:I→ℂ=>P f+R f ):= by
    obtain ⟨A,rfl⟩:= h; obtain ⟨B,rfl⟩:= hx; let T:Pencil I F:= ⟨Sum A.site B.site,inferInstance, Sum.elim A.send B.send, Sum.elim A.mapS B.mapS⟩; refine ⟨ T,?_⟩; funext f; unfold Pencil.prime; change _= (∑ i:A.site ⊕ B.site, Sum.elim A.mapS B.mapS i ( f ( Sum.elim A.send B.send i ) ) ); rw [ Fintype.sum_sum_type ]; rfl
lemma comp (T:F→L[ℝ]D)(h:Stencil P): Stencil (T ∘ P):= by
    obtain ⟨p,rfl⟩:= h; refine ⟨ ⟨ p.site,p.finS,p.send, fun i=> T ∘L p.mapS i ⟩,?_⟩; funext k; unfold Pencil.prime Function.comp; rw [map_sum]; rfl
lemma cap {f:J→(I→ℂ)→F}(T:Finset J)(h:∀ i∈T, Stencil ( f i )): Stencil (fun k:I→ℂ=> ∑ i∈T,f i k):= by classical induction T using Finset.induction_on with| empty=> rw [show (fun k:I→ℂ=> ∑ i∈(∅:Finset J),f i k) = 0 from funext fun _=> Finset.sum_empty]; exact zero| insert i s hi ih=> simp only [ Finset.sum_insert hi ]; exact add ( h _ (by simp )) ( ih ( fun i hi=> h i (Finset.mem_insert_of_mem hi)))
lemma before (P:(I→ℂ)→ F)(A:J→I){B:(J→ℂ)→ F}(hp:Stencil (I:=J) B)(h:∀ f:I→ℂ,P f=B (f∘ A)):Stencil P:= by obtain ⟨V,rfl⟩:= hp; exact ⟨ ⟨ V.site,V.finS, A ∘ V.send,V.mapS⟩, funext h ⟩
end Stencil
section cost
variable {s:Set E} {f:I→ E→ℂ} {A:I→( I→ℂ ) → E→L[ℝ]ℂ} (h:IsOpen s)
-- argument order x implicit.NeBot.Domain
abbrev Cochain (A:I→(I→ℂ)→ E→L[ℝ]ℂ)(f:I→ E→ℂ)(s:Set E): Prop:= ∀ i x,x∈s→ HasFDerivAt ( f i ) ( A i ( fun j=> f j x ) ) x
variable (ht: Cochain A f s) (hp:∀ i,Stencil ( A i ))
include h ht hp
lemma chainM (n:ℕ)(i:I): ContDiffOn ℝ n ( f i ) s:= by
    induction n generalizing i with
    | zero=> exact contDiffOn_zero.mpr fun x hx=> ( ht i x hx |>.continuousAt ).continuousWithinAt
    | succ n ih=> obtain ⟨C,hC⟩:= hp i; rw [ Nat.cast_succ ]; refine ( contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (IsOpen.uniqueDiffOn h) ).mpr ⟨ by simp, fun x=> _,?_ ,fun x hx=> ( ht i x hx ).hasFDerivWithinAt ⟩; rw [hC]; exact ContDiffOn.sum (fun i hi=> (C.mapS i).contDiff.comp_contDiffOn (ih _))
omit h ht
variable {Z:I→ℝ→ E→ℂ}{t:ℝ→ Set E}{K:Set E}
variable (hQ:∀ᶠ r:ℝ in atTop, K ⊆ t r ∧ IsOpen ( t r ) ∧ Cochain A (fun i=> Z i r) ( t r ))
variable (hv:∀ i, Rain p ( fun (x:↥K) r=> Z i r x.val ))
include hQ hv
lemma harmonics (n:ℕ)(i:I): Rain p ( fun (x:↥K) r=> iteratedFDeriv ℝ n ( Z i r ) x.val ):= by
    induction n generalizing i with
    | zero=> exact DerivD.across (hv i) ( Eventually.of_forall fun p x=> le_of_eq (norm_iteratedFDeriv_zero ..) ) -- args
    | succ n ih=>
       obtain ⟨F,hF⟩:= hp i; let V (j:F.site)(x:↥K)(r:ℝ):= ( F.mapS j ).compContinuousMultilinearMap (iteratedFDeriv ℝ n ( Z ( F.send j ) r ) x.val );
       have ht(c:F.site): Rain p ( V c ):= throughF ( ih ( F.send c ) ) _ ‖F.mapS c‖ (norm_nonneg _) ( F.mapS c ).norm_compContinuousMultilinearMap_le
       apply DerivD.across ( Rain.sum Finset.univ (f:=V) ( fun i _=> ht i ) ); filter_upwards [ hQ ] with r h x; let W:= fun (j:F.site) (p:E)=> ( F.mapS j ) ( Z ( F.send j ) r p ); have he := fun i=> ( chainM h.2.1 h.2.2 hp n i ).contDiffAt ( h.2.1.mem_nhds ( h.1 x.property ) );
       have hh : fderiv ℝ ( Z i r ) =ᶠ[𝓝 x.val] fun p:E=> ∑ j:F.site, W j p:= eventuallyEq_of_mem ( h.2.1.mem_nhds ( h.1 x.property ) ) (fun y hy=> by rw [(h.2.2 i y hy).fderiv, hF ]; rfl )
       rw [ ← norm_iteratedFDeriv_fderiv, ( hh.iteratedFDeriv ℝ n ).eq_of_nhds, iteratedFDeriv_fun_sum_apply ( f:= W ) ( fun i hi=> ( F.mapS i ).contDiff.contDiffAt.comp _ (he ( F.send i )) ) ]; refine le_of_eq (congr_arg _ ( Finset.sum_congr rfl fun j _=> ( F.mapS j ).iteratedFDeriv_comp_left ( he ( F.send j ) ) le_rfl ))
end cost
end YM.FVA2.DerivD
