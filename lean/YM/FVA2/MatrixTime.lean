import YM.FVA2.BufferGroup
/-!
# Coherent MatrixTime unit-adjoint scaling operation. Δ_{exp y} acts with `-d y` exponent.
 A whole system on nested labels to simplify proof composition later.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 240000
namespace YM.FVA2.Verne
open Set Function Filter Pert Pert.Position Maxwell Maxwell.Free PositionX PositionX.Jet PositionX.Ribbon PositionX.Detector Elegant PayAll ColorCode MS.Menus Real
open scoped Topology ContDiff Classical
variable {G:Gauge} (F: Labels.Frames G) (v x:ℝ)(k m d:ℕ)
abbrev factor (v:ℝ)(d:ℕ): ℝ:= Real.exp (- ( d:ℝ ) * v)
lemma factσ (x y:ℝ)(k:ℕ) : factor x k * factor y k = factor ( x+y ) k:= by unfold factor; rw [← Real.exp_add, mul_add ]
def Δ (F:Labels.Frames G)(v:ℝ)(d:ℕ): Module.End ℂ (E F d):= eng F (factor v) d
lemma Δ_apply (p:E F d): Δ F v d p= eng F (factor v) d p:= rfl
lemma Δ_sum (s t:ℝ): Δ F (s+t) d=(Δ F s d) ∘ₗ (Δ F t d):= by
    apply (sameAxis F d).ext; intro i; unfold Δ; rw [LinearMap.comp_apply,massX,massX,map_smul,massX,smul_smul,← Complex.ofReal_mul,mul_comm,factσ ]
lemma Δ_0 : Δ F 0 d = LinearMap.id:= by
    apply (sameAxis F d).ext; intro i; rw [Δ,massX]; simp [ factor ]
lemma Δ_basis (v:BasisIx G d): Δ F x d (sameAxis F d v)= (factor x v.size:ℂ) • sameAxis F d v:= massX ..
-- corresponding additive increment. life not light.
def Øb : Buffer F d:= let A:= eng F ( factor x ) d-LinearMap.id; ⟨ (A.restrictScalars ℝ).toContinuousLinearMap, by
    refine ⟨?_,fun k hk v hv=> ?_,fun v=> ?_,fun s v=>?_,map_smul A _⟩
    · change A _= _; unfold A; rw [LinearMap.sub_apply,starUnit]; simp [factor ]
    · change eng F (factor x) d v - v∈_; exact (lower F k d).sub_mem (preserveφ F (factor x) v hv hk.le) hv
    · change (Model F).conj (hierarchy F).spin d ( A v )= A ((Model F).conj (hierarchy F).spin d v); unfold A; rw [LinearMap.sub_apply,LinearMap.sub_apply,map_sub,starφ ]; rfl
    change Extra.FD.rideO F s.ortho _ ( A v )=A _; unfold A; simp_rw [LinearMap.sub_apply,map_sub ]; rw [ ← ride ]; rfl ⟩
lemma frame_Øb : frameC F (Øb F x d)= Δ F x d:= by apply LinearMap.ext; intro v; change v + (Δ F _ _ v - v)=_; abel
lemma clear : Øb F 0 d=0:= by apply frameC_i; rw [frame_Øb,frameC_zero,Δ_0]
lemma sequenced : Øb F (x+v) d = settled (Øb F x d, Øb F v d):= by apply frameC_i; rw [frame_Øb, frame_settled,frame_Øb,frame_Øb,Δ_sum]
lemma focusedØ : withinBlock F (Øb F x d) = Øb F x d:= by
    apply ( recognized F _ ).2; intro i j he; change (sameAxis F d).coord j (Δ F x d ( sameAxis F d i )-sameAxis F d i)=0; rw [Δ_basis,map_sub,map_smul ]; have hv:i≠j:=fun h=> he (h ▸ rfl); simp [Module.Basis.coord_apply,hv] -- Dec eq
variable {F d}
local notation "B0"=> Buffer F d
local infixr:70 " ◃ "=> luxury
lemma transported (a b:Word (Buffer F d)){e:ℕ} (L: B0→ₗ[ℝ] Buffer F e)(h:∀ a b:B0,L (followB a b)=followB ( L a ) ( L b )): L ∘ (a ◃ b)=(L ∘ a) ◃ (L ∘ b):= by
    have he(a b:B0): L ( settled (a,b) )=settled (L a,L b):= by unfold settled; rw [map_add,map_add,h]; -- lint
    funext n; let f:=delay a n; let g:=delay b n; let T : B0→L[ℝ] Buffer F e:=LinearMap.toContinuousLinearMap (𝕜:=ℝ) (E:=Buffer F d) (F':=Buffer F e) L; have hf:Act n f a:= Act.swell a le_rfl; have hg:Act n g b:= Act.swell b le_rfl;
    have hs(f:ℝ→B0)(v:Word (Buffer F d))(h:Act n f v): Act n (L ∘ f) (L ∘ v):= by exact Act.linear (E:=Buffer F d) (G:=Buffer F e) (L:=T) h
    have hK:Act n (fun i=> settled ( f i,g i ) ) (a ◃ b):= (hf.zipper hg).transit settled_diff.contDiffAt
    have hm : Act n (fun i=> L ( settled ( f i,g i ) )) ( L ∘ ( a ◃ b ) ):= hs _ _ hK; simp_rw [ he ] at hm; exact hm.trans_at ((((hs f _ hf).zipper ( hs g _ hg ))).transit ( m:=settled ) settled_diff.contDiffAt ) le_rfl
variable (a b:Word (Buffer F d))
lemma tgrade : withinBlock F ∘ (a ◃ b) = (withinBlock F ∘ a) ◃ (withinBlock F ∘ b):= transported a b (withinBlock F) ( hom F ) -- syntax
lemma followV (a b:Buffer F d) (h:k≤d): zoomL F h (followB a b)=followB (zoomL F h a) (zoomL F h b):= by apply follows_right; apply LinearMap.ext; intro v; apply up_inj F h; rw [bufferL_eq,zoomL_eq]; change a.1 (b.1 (up F h v))= up F h ((zoomL F h a).1 ((zoomL F h b).1 v)); rw [ zoomL_eq, zoomL_eq ] -- dir
lemma zoomT (h:k≤d): zoomL F h ∘ (a ◃ b)=(zoomL F h ∘ a) ◃ (zoomL F h ∘ b):= transported a b (zoomL F h) (fun a b=> followV k a b h)
-- nested Grain network
structure Strat (F: Labels.Frames G) where
    wire (d:ℕ) : Word ( Buffer F d )
    proceeds {d e:ℕ}(h:d≤e): zoomL F h ∘ wire e= wire d
namespace Strat

@[ext] lemma ext {v w: Strat F}(h:∀d,v.wire d=w.wire d): v=w:= by cases v; cases w; congr; exact funext h
instance : Mul (Strat F):= ⟨fun a b=> ⟨ (fun i=> a.wire i ◃ b.wire i), fun {_ _} h=> by rw [ zoomT _ _ _ h, a.proceeds h,b.proceeds h ]⟩⟩
def Λ (F:Labels.Frames G)(x:ℝ): Strat F:= ⟨ fun d=> just ( Øb F x d ), fun {d e} h=> by
       have he : zoomL F h ( Øb F x e )= Øb F x d:= by apply follows_right; apply LinearMap.ext; intro p; apply up_inj F h; rw [ bufferL_eq,zoomL_eq ]; change eng F _ _ (up F h p)-up F h p=up F h (eng F _ _ p-p); rw [map_sub,show eng F _ e _=_ from LinearMap.congr_fun ( riseφ F (factor x) h ) p]; rfl
       funext i; unfold just; simp_rw [Function.comp_apply]; split; exact he; exact map_zero _ ⟩
lemma pay (v w:Strat F)(i:ℕ): (v*w).wire i=v.wire i ◃ w.wire i:= rfl
instance : One (Strat F) where
    one:=Λ F 0
instance : Monoid (Strat F) where

    mul_assoc a b c:= ext ( fun i=> assocH _ _ _ )
    one_mul a:= ext (fun i=>by rw [pay,show ( ( 1 :Strat F ).wire i )=0 from ?_, lIdent ]; change just ( Øb F 0 i )=0; rw [ clear,justZ ])
    mul_one a:= ext (fun i=>by rw [pay,show ( ( 1 :Strat F ).wire i )=0 from ?_, rIdent ]; change just ( Øb F 0 i )=0; rw [ clear,justZ ])
lemma zeroed (F: Labels.Frames G)(i:ℕ): ( (1:Strat F).wire i )=0:= by change just ( Øb F 0 i )=0; rw [clear,justZ ]
lemma Λwire (x:ℝ)(d:ℕ): (Λ F x).wire d=just (Øb F x d):= rfl
lemma east : Λ F x*Λ F v=Λ F (x+v):= ext fun d=> by rw [pay,Λwire,Λwire,justH,← sequenced ]; rfl
lemma south {v:ℝ}: Λ F (-v) * Λ F v=1:= by rw [east, neg_add_cancel]; rfl
lemma north {v:ℝ}: Λ F v * Λ F (-v)=1:= by rw [east, add_neg_cancel]; rfl
-- Δ not stable. but included inverse.
def resume (p: Strat F) (u:Word ℝ): Strat F:= ⟨fun i=>ren u (p.wire i),fun {d e} h=> by rw [ Jet.ren_writes (zoomL F h), p.proceeds ] ⟩
def only (u:Strat F): Strat F:= ⟨ fun i=> withinBlock F ∘ u.wire i, fun {d e} h=> by
    funext j; change zoomL _ h (withinBlock _ _) = withinBlock _ _ ; rw [ zoomBlock, show zoomL F h _= _ from congr_fun ( u.proceeds h ) j ] -- _
  ⟩
def pulse (p:Strat F): Prop:=∀ d,Stable (p.wire d)
variable (r t u: Strat F) {φ v: Word ℝ}
lemma initial : pulse (1:Strat F) := fun i=>(zeroed F i).symm ▸ rfl
lemma pulse.grow (hr:r.pulse)(ht:t.pulse): Strat.pulse (r*t):= fun i=> stack _ _ ( hr i ) ( ht i )
lemma pulse.near (h:pulse r) (ht:light φ): pulse ( resume r φ ):= fun i=> fast _ ( h i ) ht
lemma pulse.adj (h:pulse r): pulse ( only r ):= fun i=> ( by change withinBlock F ( r.wire i 0 )=0; rw [ show r.wire i 0=0 from h i,map_zero ] )
lemma resume_wire (i:ℕ)(f: Word ℝ) : (resume r f).wire i= ren f (r.wire i):= rfl
lemma resumeT (h:light φ) : resume (r*t) φ= resume r φ * resume t φ:= ext fun i=> renH (r.wire i) (t.wire i) h
lemma resumeM (h:light φ)(hx: light v): resume (resume r v) φ=resume r (ren φ v) := ext fun i=> Jet.asc (V:=Buffer F i) h hx (r.wire i)
lemma resume0 (u: Word ℝ): resume (1:Strat F) u=1:= ext fun i=> by rw [resume_wire, zeroed]; funext j; unfold ren order; simp
lemma resetR (t:ℝ)(h:light φ): resume (Λ F t) φ=Λ F t:= ext fun i=>by rw [resume_wire,Λwire, Jet.ren_static ( Øb F t i ) h ]
lemma only_wire (r:Strat F)(i:ℕ): (only r).wire i= withinBlock F ∘ r.wire i:= rfl
lemma onlyT : only (r*t)=only r * only t:= ext fun i=> tgrade (r.wire i) (t.wire i)
lemma onek : only (1:Strat F)=1:= ext fun i=> by rw [ only_wire,zeroed]; exact funext fun k=>map_zero _
lemma onlySeq (v:ℝ): only (Λ F v)=Λ F v:= ext fun i=> by rw [only_wire,Λwire ]; funext k; simp only [Function.comp_apply]; unfold just; split <;> first| exact focusedØ ..| exact map_zero _
lemma iconic : only (resume r φ)=resume (only r) φ:= ext fun i=> ren_writes (withinBlock F) φ (r.wire i) -- expected type defeq?
lemma diagonal_o : only (only r)=only r:= ext fun i=> funext fun j=> diagonal F (r.wire i j)
lemma resumeHead : resume r headway=r:= ext fun i=> by rw [resume_wire]; exact ren_head (V:=Buffer F i) _
-- relies on detector existence not new assumption. required already for H normalization.
def refresh (D: (d:ℕ)→ Detector F d)(p:Strat F)(h:p.pulse): Strat F:= ⟨ fun i=> undo (p.wire i) ( D i ), fun {d e} he=> (unique (p.wire d) (zoomL F he ∘ undo (p.wire e) (D e)) (D d) (h d) (by rw [← p.proceeds he, ← zoomT _ _ _ he, (won _ _ (h e)).2 ]; exact funext fun i=>map_zero _)) ⟩
lemma right_refresh (D:(d:ℕ)→ Detector F d)(p:Strat F)(h:p.pulse): (refresh D p h).pulse ∧ p*refresh D p h=1 ∧ refresh D p h * p=1 := by
   refine ⟨ fun i=> (won _ (D i) (h i)).1, ext fun i=>?_, ext fun i=>?_⟩; · rw [zeroed]; exact (won _ ( D i ) ( h i )).2
   rw [zeroed]; exact reverse _ ( D i ) (h i)
end Strat
end YM.FVA2.Verne
