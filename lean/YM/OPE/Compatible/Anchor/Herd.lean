import YM.OPE.Compatible.Anchor.Top
/-!
# Generator angular vector tensors.Lift operation everywhere. Root vector.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset Labels
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Work.F08
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer AnalyticNext.QuarticMatch.Joint Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver FreeResolvent WithLp
open Drift Char Silt Silt.Float Module Page Planned.PrimaryIntegral295.Carrier
variable {i j d k m r n l:ℕ}{Z I J M E F:Type}
variable {K:Sponsor G}{S:Seasons K}{u:M→ℝ}{v:ℝ}{τ:Phase→ℕ}
local notation "Ξ"=>solar G d τ
local notation "θ"=> 𝓝[>] (0:ℝ)
variable {z:M→ℝ}{R:Alphabet G k→ℝ}(L:M→Submodule ℝ (solar G d τ))
lemma Obtains.smul (h:Obtains z L r n R)(a:ℝ): Obtains z L r n (a • R):=by
     obtain ⟨c,hc,H⟩:=h.stock; refine ⟨‖a‖*c,by positivity,fun i=>?_⟩; obtain ⟨v,hp,hv,ht⟩:=H i; refine ⟨a • v,?_,(L i).smul_mem a hv,ht.smul a⟩; rw[norm_smul]; exact (mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans_eq (by ring)
lemma Obtains.plus {V:Alphabet G k→ℝ}(h:Obtains z L r n R)(hV:Obtains z L r n V)(ht:r*k≤τ 0): Obtains z L r n (R+V):=by
     obtain ⟨c,hc,H⟩:=h.stock; obtain ⟨a,hq,Q⟩:= hV.stock; refine ⟨c+a,by positivity,fun i=>?_⟩; obtain ⟨v,hp,hv,h⟩:= H i; obtain ⟨x,he,hx,H⟩:= Q i; refine ⟨v+x,?_,(L i).add_mem hv hx,h.add H ht⟩; rw [add_mul]; exact (norm_add_le ..).trans (add_le_add hp he)
lemma Obtains.zen : Obtains z L r n (0:Alphabet G k→ℝ):=by apply RoomN.get (f:=0) L (RoomN.zen L); intro i x; change Tendsto (fun y:ℝ=> (y^_)⁻¹ • (0:ℝ)) θ (𝓝 (0:ℝ));simp
lemma Obtains.sum (s:Finset I)(y:I→Alphabet G k→ℝ)(hs:∀ i∈s,Obtains z L r n (y i))(hp:r*k≤τ 0): Obtains z L r n (∑ i∈s,y i):=by induction s using Finset.induction_on with
    | empty=>rw[sum_empty]; exact Obtains.zen L
    | insert i s hi ih=>rw [sum_insert hi]; exact Obtains.plus L (hs _ (mem_insert_self ..)) (ih fun j hj=>hs _ (mem_insert_of_mem hj)) hp
abbrev Wakeful (Y:Alps K S i v)(Q:Submodule ℝ (solar G d τ)) :Prop:=∀ (r:ℕ) (_hp:r+1≤d) (o:RootEdge) (K:Finset RootEdge) (g:Libra.Keys G (↥K)→ G.Color), BudY o false r (fun i:↥K=>i.val) g→∀ p:solar G d τ,Holds p (SongY Y o r (fun i:↥K=>i.val) g)→p∈Q
variable (A:(j:M)→Alps K S i (u j)){α:Fin r→Fin k}(Fθ:SpiceK G α)
structure Forum (A:(j:M)→Alps K S i (u j))(L:M→Submodule ℝ (solar G d τ)):Prop where
    taxes : ∀ i,Wakeful (A i) (L i)
    enough : 4 ≤ i
    pays : 0 ≤ u
    stable : ∃ c:Clip,∀ i,(A i).clip=c
variable (hp:(r+1)*k ≤ τ 0)(h:Forum A L)
lemma farm_s (e:RootEdge)(he:r+1≤d)(hp:(r+1)*k ≤ τ 0)(hv:G.Simple)(hf:Abalo Fθ) (h:Forum A L):
     RoomN (ZTheta u) L (fun i (x:fieldX (Shade G))=> Dotty (rootζ (A i) x e) (ClearW Fθ x)) (r+1) k :=by
       obtain ⟨s,f,hQ,hX⟩:=tradeP Fθ e hf; obtain ⟨p,hp'⟩:=h.stable; obtain ⟨c,hc,H⟩:= globuleY (τ:=τ) e false A (fun i:↥s=>i.val) f hQ he hp' h.pays hv -- args
       refine ⟨_,hc,fun i=>?_⟩; obtain ⟨v,hy,hv'⟩:= H i; refine ⟨v, hy,h.taxes _ r he e s f hQ _ hv',PegS _ hv hQ hv' he,fun z h'=>?_⟩; rw [Fler _ hv hQ (show Holds _ (SongY (A i) e r _ _) from hv') he (h.enough) h' hp]; unfold Dotty InkS; simp_rw [hX]
-- training stencil assembly by induction on ordered moves.Consumer helper.
lemma train_s (p:Fin j→Axis)(i:Cover):∃ (s:Finset Cover)(c:Cover→ℝ),∀ v:Cover→ℝ,trainX ℝ j p v i=∑ x∈s,c x*v x:=by
     let U: (Cover→ℝ)→ₗ[ℝ]ℝ:= LinearMap.proj i ∘ₗ trainX ℝ j p; have he: Realm U:=realmTrain (Y:=fun i=>i) (by intro i; refine ⟨{i},fun x y hs=> hs (by simp : i ∈ ({i}:Finset _))⟩) p i -- args
     obtain ⟨s,A,h⟩:=projectionExists U he; let f(y:Cover):= if H:y∈s then A (Pi.single (M:=fun _:↥s=>ℝ) (⟨y,H⟩:↥s) 1) else 0; refine ⟨s,f,fun v=>?_⟩; let V:↥s→ℝ:= fun t=>v t.val; rw [← Finset.sum_coe_sort]; change U v= ∑ t:↥s, f _ * _; rw [h]; change A V=_; nth_rw 1 [show V= ∑ i:↥s,V i • (Pi.single (M:=fun _:↥s=>ℝ) i 1) from (by ext i; rw[Finset.sum_apply]; simp [Pi.single_apply,Finset.sum_ite_eq])]; rw [map_sum]; apply sum_congr rfl; intro j _; rw [map_smul]; unfold f; rw[dif_pos j.property]; change V j * _=_; exact mul_comm _ _
lemma cueD (w:Axis)(B:Fin j→Axis) (x:Alphabet G k)(g:Fin k)(hg:g.val=j+1)(p:Cover) (F:Taylor G (j+1))(hF:hg ▸ x g=F)(hs:i≥4)(t:M) : BillUp ℝ (j+2+rankX α) (fun s:ℝ=>Dotty (wageZ (A t) B (showerW k s x) w p) (ClearW Fθ (showerW k s x))) (Dotty ((-((j+1).factorial:ℝ)) • flame F w (basis ∘ B)) (Fθ (fun i=> x (α i)))):= UpDot (flareM hs x g hg B p w F hF) (coupT α Fθ x)
end YM.OPE.Variance
