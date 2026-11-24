import YM.OPE.Compatible.Lob.Candle
/-!
# H.Launch supplies.Born.Cumul integrations at Mark. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Quit.Jac
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P:Patch}{R:ChartRatio G}{C:KernelChoices}{p:Clip}
variable {v v' b:ℝ} {A:Alps K T i v}{D:Alps K T j v'}{U:Boxes G P K.K}
local notation "Y!"=> solar G d τ
local notation "T!"=> Tracts G d τ
open PriceZ
local notation "L!"=> Tower (Shade G) d τ
local notation "D!"=> Shade G
local notation "Y"=> solar G d τ
open JetS
variable (h:Aware d τ)
lemma faithful (a b:L!)(ha:Rainbow (Drift.spread G d τ a))(hb:Rainbow (Drift.spread G d τ b))(hp:∀ n:Side,∀ x: Bid.Dir G n,Vtap a 0 x = Vtap b 0 x): a=b:= bloomP G d τ (MsUnique (resin a (m:=0) (fun _=>by omega)) (resin b (m:=0) (fun _=>by omega)) ha hb hp) -- change
variable (hp:LocalRatio R)(hs:G.Simple)
lemma boneS (v: Token): (Ū*v).seq 0=0:= zero_mul _
lemma boneL (v:Token): (Ū*v).seq 1=v.seq 0:=by change 0* _+1*_=_; rw [zero_mul,zero_add,one_mul];rfl
lemma boneH(v:Token):(Ū*v).seq 2=v.seq 1:=by change 0*_+1*_+0*_=_; rw [zero_mul,one_mul,zero_mul,add_zero,zero_add];rfl
lemma pulseA {u:ℝ}(q:Town A D U R u)(x:Y): trellisA G h (yankV D q hp hs h x)=yankV D q hp hs h (trellisA G h x):=by
      let C:= Candy G h; let p:=x.val; let T:=actor A U R 0 ⟨hs,hp,q.eph⟩ h
      suffices hx:C (T p)=T (C p) by apply Subtype.ext; change C (rebase G h (-u) (T p))=rebase G h (-u) (T (C p)); rw [show C (rebase _ _ _ _)=_ from gaze h (T p) (-u),hx]
      have he: T p∈ solar G d τ:= actors 0 A _ _ _ _ _ x.property; have ht:= x.property; apply faithful _ _ (sailV h (⟨T p,he⟩:Y)|>.1) ((show T (C p)∈solar G d τ from actors 0 A _ _ _ _ _ (sailV h x)).1); intro n y; obtain ⟨X⟩:= mach P K.K U A (0:ℝ) q.eph hs n
      let f(w:L!)(i j):= X.atW R 0 y i d j (Drift.spread G d τ w); have hF(w:L!)(i:Phase): Tendsto (fun j:ℕ=>f w j i) atTop (𝓝 ((Vtap (T w) 0 y).seq i.val)):=Foz _ _ _ _ h w X 0 y i -- need solve
      have he(k:ℕ)(i:Phase): f (C p) k i=(Ū * TracePay (subStud P K.K (X.jet k)) P.odd_side U A (X.stems k) (X.paths k) R d (Drift.spread G d τ p) 0 (wrap _ (lift (0:Site n))) (X.traceX k) (Booklet (X.yarn k) G y)).seq i.val:=by
           unfold f Cola.atW; let t:=X.jet k; let V:= Booklet (X.yarn k) G y; let a:= wrap t (lift (0:Site n)); let S:=subStud P K.K t; let Q:= X.traceX k; let t':= X.stems k; let g:= X.paths k; let p':= Drift.spread G d τ p; let Γ(w: Muse G):=TracePay S P.odd_side U A t' g R d w 0 a Q V; have hx:Γ (Drift.spread G d τ (C p))=Ū * Γ p':=by
               unfold Γ; rw [timely,timely]; let J:= bitH A S P.odd_side t' U g a V Q p' d; rw [show bitH A S _ t' U g a V Q _ d=fun i=> Ū * J i from funext fun i=> (show _= _ from congr_fun (Speel h p (S.ratio.embed a)) _)]; exact coin_F _ _ _ _ J (bitB A S _ t' U g a V Q p' (resin p (m:=0) (fun _=>by omega))) (flared A R S P.odd_side t' U g V Q hp)
           exact congr_arg (fun a:Token=>a.seq i.val) hx
      rw [show Vtap (C (T p)) 0 y= _ from congr_fun (Speel h (T p) _) y]; apply JetS.eta
      · have hV(j:ℕ): f (C p) j 0=0:=by rw [he j 0]; exact boneS _
        have hb:= tendsto_nhds_unique_of_eventuallyEq (hF (C p) 0) (show Tendsto (fun _:ℕ=>(0:ℝ)) atTop (𝓝 0) from tendsto_const_nhds) (.of_forall hV); rw [ml_s]; exact (zero_mul _).trans hb.symm
      · have hV(j:ℕ): f (C p) j 1=f p j 0:=by rw [he]; exact boneL _
        rw [ml_l]; change 0*_+1*_= _; rw [zero_mul,zero_add,one_mul]; exact tendsto_nhds_unique_of_eventuallyEq (hF p 0) (hF (C p) 1) (.of_forall fun j=>(hV j).symm)
      have hV(j:ℕ): f (C p) j 2=f p j 1:=by rw [he]; exact boneH _
      rw [ml_h];change 0*_+1*_+ 0*_ = _; rw [zero_mul,zero_add,one_mul,zero_mul,add_zero]; exact tendsto_nhds_unique_of_eventuallyEq (hF p 1) (hF (C p) 2) (.of_forall fun j=>(hV j).symm)
lemma spinC (a:Axis)(x:Y): spose a G d τ (trellisA G h x)= trellisA G h (spose a G d τ x):=by
     apply Subtype.ext; apply faithful _ _ ((spose a G d τ (trellisA G h x)).property.1) ((trellisA G h (spose a G d τ x)).property.1) -- change
     intro n i; let V:= trellisA G h x; rw [show Vtap ((spose a G d τ V).val) _ i= _ from (show Vtap (Mirror a G d τ V.val) _ i=Vtap V.val (dart a 0) (streak a G n i) from toner a V.val (0:Site n) i)]; rw [show _= _ from (show Vtap V.val (dart a (0:Site n)) (streak a G n i)= _ from congr_fun (Speel h x.val _) _)]; change Ū*_= Vtap (Candy G h (Mirror a G d τ x.val)) _ i; rw [Speel]; exact congr_arg _ (toner a x.val 0 i).symm
end YM.OPE.Quit.Jac
