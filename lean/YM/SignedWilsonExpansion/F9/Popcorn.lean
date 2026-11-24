import YM.SignedWilsonExpansion.F9.Fence
/-!
# Consumers at finite aperture: projected comparison ballots (off Maxwell shell restored)

All higher-rank habits and Wick part may be read before clocks start. Proper faces
use same shelf in both worlds. Updates below with Signed.rotate and `compensated`
quest DON'T allow spinning the noise on the physical K file.
-/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa.StationA
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge Matrix
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos PathCost FVA2
open Cloth XSpace
open PertExtension PertExtension.Orb FormalOPE FormalOPE.RG10 FormalOPE.RG10.InversionWard
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical ENNReal InnerProductSpace
variable {G:Gauge}{H:Hol G}{h i j k a m r d n l:ℕ}{F:Frame G h}{x:Label G h}{P:Period} {s:Side} {ι:Type*}
open Pill
section
variable (T:P.Tree)(A:XSpace.Survey G H h)(R:Rays G h H)(x:Site P.side)
    (t:Signed)(v:Label G h)(p:v∈Grade (h,r))(q:realBar v=v)(hr:r≤h)
local notation "Q"=>Labels.tensor t.ortho
lemma stirred {v: Label G h}(p:v∈Grade (i,j)): tensor t.ortho v∈Grade (i,j):=by
    have he:= gradePart_mem (i,j) (tensor t.ortho v); rwa [gradePart_turn,gradePart_self v _ p] at he
lemma admit_roll {i j}(p:v∈Grade (i,j)): (curlP A v p).spins t=curlP A _ (stirred t p):=by
   refine Cloth.same _ _ ?_ rfl
   funext U; apply congr_arg (fun x:ℂ=>x.re); unfold title evaluateLabel; simp only [Function.comp_apply]; rw [A.reading_signed, snap_expand]; exact (eval_changed ..).symm
lemma turned_card : rotate t r (permitT A p)=permitT A (stirred t p):=by
   let Y:=tensor t.ortho v; have hy:= stirred t p
   have hn {f g:Pill G} (q:f=g)(i:f.rank≤ r)(l:ℕ): ∀ v:g.rank≤r, overC f i l= overC g v l:=by intro _; subst g; rfl
   have hh (j:ℕ)(i:ℕ): gradePart (i,j) (Press.diff A Y)= Q (gradePart (i,j) (Press.diff A v)):= by rw [Press.diff,Press.diff,A.wick_signed, show Y= Q v from rfl,← map_sub Q,gradePart_turn]
   have hN (i:Fin (h+1))(j:Fin r): rotate t r (overC (pigment A p i j) j.isLt.le 0)= overC (pigment A hy i j) j.isLt.le 0:=by
        rw [Cloth.rolled]; apply hn; unfold pigment; rw [admit_roll]; -- congr 1 might be bad; f equal via eq. cast
        have hv : ∀ (x y: Label G h)(z:x=y)(p:x∈ Grade (i.val,j.val))(q:y∈Grade (i.val,j.val)), curlP A x p=curlP A y q :=by intro x y z p q; subst y; rfl
        exact hv _ _ (hh _ _|>.symm) _ _
   have hW:(rotate t r) (overC (curlP A v p) (Eq.le (by rfl)) 0) = overC (curlP A Y hy) (Eq.le (by rfl)) 0:=by rw [Cloth.rolled]; exact hn (admit_roll A t v p) _ _ _
   unfold permitT; rw [map_add,map_sum]; apply congr_arg₂ (·+·) hW; simp_rw [map_sum]; exact Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl (fun j _=> hN i j)
include q hr in
lemma permit_turn : requesting T x r (rotate t r (permitT A p)) = XSpace.Bare.column T A x (tensor t.ortho v):=by
   rw [turned_card A t v p]; exact pinwheel T _ (stirred t p) (by rw [real_turn,q]) x A hr
-- pay rotated hedge
lemma Ward_quiet {v:Label G h}(p:v∈Grade (h,r+1)){S:Finset Cover}(hY:R.FitsAt S)(hv:FitsIn S P.side)(Y:ℕ)(hc:cord S≤Y)(hb:2*Y < separation x (-x)) : SameV T x Y (requesting T x (r+1) (rotate t _ (hedge R p))) 0:=by
   let M:= toTensor (r+1) v; let P':=holder R M (tensor_eqv p); let L:=sink R M (tensor_eqv p); let U:= P'.spins t; let V:= L.spins t; let u:= places x U.f; let v:= places x V.f
   refine ⟨fun i f A hq hf rs ht hl=>?_⟩; have hg:=even_iff_two_dvd.mpr P.even; have he'':2*cord S < separation x (-x):=by omega
   have he: Bare.normalized T G (X^U.rank*propose T x U*(X^i*A))= X^2*Bare.normalized T G (X^V.rank*propose T x V*(X^i*A)):=by
       rw [hq,apex,apex, ←mergeBook T (flies _ U.valid _) ht,←mergeBook T (flies _ V.valid _) ht]; have hx:=hf.active rs; let H:=InversionTop.Uses.pre_mul (candle U x) hx; let Z:= InversionTop.Uses.pre_mul (candle V x) hx; rw [sameBook T H, sameBook T Z]; exact payment hg H Z (measureTurn hg R hY M (tensor_eqv p) x Y hv hc he'' t hl hf)
   unfold hedge; rw [map_sub,Cloth.rolled,Cloth.rolled,map_sub,request_crest,request_card, zero_mul,map_zero,sub_mul,map_sub,sub_eq_zero]
   apply mul_left_cancel₀ (a:=PowerSeries.X^(U.rank+i)) (pow_ne_zero _ X_ne_zero); rw [←tunic,←tunic]; let a:=propose T x U; let b:=propose T x V
   change Bare.normalized T G (X^(U.rank+i)*(a*A)) = Bare.normalized T G (X^(U.rank+i)*(X^(shadeShift r)*b*A)); rw [show (PowerSeries.X^(U.rank+i)*(a*A))= X^U.rank*a*(X^i*A) by rw [pow_add];ring, show (PowerSeries.X^(U.rank+i)*(X^(shadeShift r)*b*A))=X^2*(X^V.rank*b*(X^i*A)) from ?_,tunic]; exact he; have hu: U.rank+shadeShift r=V.rank+2:=shade_sense
   calc _ = X^(U.rank+shadeShift r)*b*(X^i*A):= by rw [pow_add,pow_add];ring
        _=_:=by rw [hu,pow_add];ring

lemma spinPr (t:Signed)(v:Label G h): (projector G h) (tensor t.ortho v)=tensor t.ortho (projector G h v) := On.section_turn _ _ _ (Maxwell.Free.pulls_label v t.ortho).symm
include q hr
lemma settled {S:Finset Cover}(hS:R.FitsAt S) (fits:FitsIn S P.side) (b:ℕ)(hv: cord S≤b)(hp:2*b<separation x (-x)) : SameV T x b (requesting T x r (rotate t _ (pricedT A R r v p))) (Bare.column T A x (projector G h (tensor t.ortho v))):=by
   cases r
   · rw [cap_beam (stirred t p),pricedT,permit_turn T A x t v p q hr]; exact SameV.gift
   rename_i r; let W:=projector G h v; let U:= hedge R (Submodule.sub_mem _ p (projector_grade p)); let Y:=requesting T x _ (rotate t _ (permitT A (projector_grade p))); let V:= requesting T x _ (rotate t _ U); have hh: v-W∈ Grade (h,r+1):= Submodule.sub_mem _ p (projector_grade p)
   rw [spinPr t v,← permit_turn T A x t (projector G h v) (projector_grade p) (fixed_color v q) hr,pricedT,map_add,map_add]; change SameV T x b (Y+V) Y; simpa only [add_zero] using (SameV.gift (A:=Y)).plus (Ward_quiet T R x t hh hS fits b hv hp)
end
end YM.WilsonCoeffUV.Mer.Xa.StationA
