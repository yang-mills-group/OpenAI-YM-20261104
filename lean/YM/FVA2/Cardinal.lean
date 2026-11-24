import YM.FVA2.LampWords
/-!
# Spacetime basis Jrad uses only Voluntary.G.P curvature choices. Build precise cone and value rule at all μ. It is useful to record expansion at all n.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 450000
namespace YM.MS.RadL
open Set Function Filter Finset MeasureTheory Real Maxwell Labels
open Analysis Tensor Koszul Plane Landau Detect Detect.Mark Local.BV InnerProductSpace Submodule Momentum Local Book.Convolve
open Theater Mach Lifting Pole Color Spray Arts Pilot Spin Motif Literal Halo Rock Path Oceans Pearl
open Complex (I)
open scoped Topology Classical ContDiff BigOperators RealInnerProductSpace
variable {G:Gauge}{d h k n m:ℕ}
namespace Spray
def pole (t:Spray) (z:ℂ)(a:G.ColorIndex)(n:ℕ):Rack G n:= ∑ i:t.Λ,(t.factor i:ℂ) • Pole_leaf z (t.plaq i) a
private def gatherτ (G:Gauge): Local.BV.Grade G→ₗ[ℂ] Law G:={ toFun:= Koszul.mono,map_add':= Koszul.mlin,map_smul':=fun x a=> Koszul.mcost a x }
lemma pole_value (s:Spray)(c:G.ColorIndex): pole s 0 c 0= Koszul.mono (s.mark c):= by
    unfold pole; change _=gatherτ G (s.mark c); rw [mark,map_sum ]; simp_rw [map_smul]; apply Finset.sum_congr rfl; intro j _; exact congr_arg (( s.factor j:ℂ ) • · ) ( Pole.singleM .. )
end Spray
section hairs
variable {I H :Type} [AddCommGroup H][Module ℂ H]
local infix:67 " ⋄ "=> product (R:=ℂ) (hands G)
private def pitch (P:H→ₗ[ℂ] H→ₗ[ℂ] H) (h:H): ∀ i:ℕ, MultilinearMap ℂ (fun _:Fin i=> H) H
 | 0=> MultilinearMap.constOfIsEmpty ℂ _ h
 | n+1=> LinearMap.uncurryLeft (M:=fun _:Fin (n+1)=>H) { toFun a:= ( P a ).compMultilinearMap (pitch P h n), map_add' a b:= MultilinearMap.ext fun p=> LinearMap.congr_fun ( P.map_add a b ) (pitch P h n p), map_smul' z a:= MultilinearMap.ext fun p=> LinearMap.congr_fun (map_smul P z a) (pitch P h n p) }
private lemma peak (P:H→ₗ[ℂ] H→ₗ[ℂ] H)(h:H) (n:ℕ)(p:Fin n→H): pitch P h n p= prodS ℂ P h n p:= by induction n with| zero=> rfl| succ n ih=> change (P (p 0)) (pitch P h n (p ∘ Fin.succ))=_;rw [ih];rfl
private lemma turnH (P:H→ₗ[ℂ] H→ₗ[ℂ] H) (h:H){f:Fin n→ Type}[∀ i,Fintype (f i)] (A:(j:Fin n)→ f j→H)(w:(j:Fin n)→ f j→ℂ) : prodS ℂ P h n (fun i:Fin n=>∑ j:f i,w i j • A i j ) = ∑ f:(i:Fin n)→f i,(∏ i:Fin n,w i ( f i )) • prodS ℂ P h n (fun i=>A i (f i)) := by
    simp_rw [← peak ]; rw [ MultilinearMap.map_sum ]; exact Finset.sum_congr rfl fun q _=> MultilinearMap.map_smul_univ ..
end hairs
abbrev roles (T: Fin m→ Spray):=(i:Fin m)→ ( T i ).Λ
def cost (T: Fin m→ Spray)(i:roles T):= ∏ j: Fin m,( T j ).factor ( i j )
def mint (T: Fin m→ Spray)(i:roles T): Fin m→ Plaq:= fun j=>( T j ).plaq (i j)
variable (T:Fin m→Spray)(σ:Lifting.Grid G m) (z:ℂ)
variable (G) in
def Word (T:Fin m→Spray)(σ:Lifting.Grid G m)(z:ℂ): Mob G:= ∑ i:roles T,(cost T i:ℂ) • Pole.saint m (mint T i) σ z
-- linear Gallery of only these words.Record at *all ζ spectrum*.
def Dome (G:Gauge)(h m:ℕ):= span ℝ {p:Coat G|∃ (T: Fin m→Spray) (σ:Lifting.Grid G m),bill T=h ∧ p= Word G T σ }
lemma wage : ∀ i:roles T,Pole.wage m (mint T i)= bill T := fun i=> Finset.sum_congr rfl fun j _=> Spray.level (T j) (i j)
lemma gallery_uses : Dome G h m≤ Gallery G m h := by
   apply span_le.mpr; rintro f ⟨ T,σ,hx,rfl⟩; have ht: Word G T σ=(∑ i:roles T,cost T i • Pole.saint m ( mint T i ) σ):= by funext v; unfold Word; rw [ Finset.sum_apply ]; rfl
   rw [ht]; exact sum_mem fun i _=> ( Gallery G m h ).smul_mem _ ( subset_span ( s:=Sentence G m h ) ⟨_,_,( RadL.wage T i ).trans hx,rfl⟩ ) -- h shadow Nat
-- explicit formula equals applying color contraction with product of Jrad, at all n ζ
private abbrev whole (T: Fin m→ Spray)(σ:Lifting.Grid G m)(z:ℂ)(n:ℕ): Rack G n:= prodS ℂ ( bite n G ) ( coin 1 ) m (fun i=> Spray.pole (T i) z (σ i) n )
lemma range_u : whole T σ z n=∑ i:roles T,(cost T i :ℂ) • Pole.wing m ( mint T i ) σ z n:= by unfold whole cost; simp_rw [Complex.ofReal_prod ]; apply turnH -- note `wing` reduc. braces.
lemma reads : Word G T σ z n= ∑ i:Lifting.Grid G m,( Lifting.group G i σ:ℂ) • whole T i z n:= by unfold Word Pole.saint; simp_rw [range_u, Finset.smul_sum, Finset.sum_apply, Pi.smul_apply ]; rw [Finset.sum_comm]; simp_rw [ smul_comm _ ((Lifting.group G _ _:ℝ):ℂ) ] -- RHS.Lens
lemma floor_t : Word G T σ 0 0 = form G m T σ:= by rw [ reads ]; unfold whole RadL.form breeze roll Lifting.family; simp_rw [prodty,pole_value ]
lemma simple : Mach.Present (Word G T σ):= Mach.Present.sum _ (fun i _=> (Pole.presence m ( mint T i ) σ).smul _) -- typing annotation
lemma slotD : Word G T σ∈ Dome G (bill T) m:= subset_span (s:={p:Coat G | ∃ (T':Fin m→Spray) (σ':Lifting.Grid G m),bill T'=bill T ∧ p= Word G T' σ'}) ⟨T,σ,rfl,rfl⟩
structure RadOK (X:Box (Mob G))(n h:ℕ)(K:Law G): Prop where
    lift:(fun z=>Literal.value (Mob G) z X)∈ Dome G h n
    fitL: X 0 0=K
lemma radial_possible (X:Law G)(hx:X∈Local.Physical.Allowed G h m): ∃ V:Box ( Mob G), RadOK V m h X:= by
    refine Submodule.span_induction (p:=fun X _=>∃ V:Box (Mob G),RadOK V m h X) ?_ ?_ ?_ ?_ (liftgram X hx)
    · rintro f ⟨ T,σ,h,rfl⟩; obtain ⟨V,hV⟩:=simple T σ;
      refine ⟨ V, hV.symm ▸ h ▸ slotD T σ,?_⟩; rw [ ← Literal.low_row V, show Literal.value ( Mob G ) 0 V=_ from congr_fun hV 0 ]; exact floor_t T σ
    · refine ⟨0,?_,rfl⟩; simp only [map_zero]; exact Submodule.zero_mem _
    · rintro f g _ _ ⟨V,hQ⟩ ⟨U,hM⟩; refine ⟨V+U,?_ ,?_⟩; simp_rw [map_add]; exact Submodule.add_mem _ hQ.lift hM.lift; rw [ Finsupp.add_apply,Pi.add_apply,hQ.fitL,hM.fitL ] -- syntax fields ok
    rintro c f hf ⟨Y,hY⟩; refine ⟨c • Y, ?_,?_⟩; simp_rw [lng]; exact Submodule.smul_mem _ _ hY.lift; rw [ Finsupp.smul_apply,Pi.smul_apply,hY.fitL ]
lemma optic {V: Box (Mob G)}{K:Law G}(hp: RadOK V m h K): Ele h m K V:= ⟨ gallery_uses hp.lift,hp.fitL⟩
end YM.MS.RadL
