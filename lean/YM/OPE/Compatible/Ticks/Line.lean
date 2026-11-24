import YM.OPE.Compatible.Ticks.Creep
/-! Individual budgets and unencumbered travel, arbitrary entrance and lower level -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Allot
open Extra.Trajectories
open Function Filter Lattice RG MergeProof Source Accent MergeProof.Float Spec Ribbons
open PhysicalNext.Repeat.Legato Bandage Ribbons.ManyCopies Ribbons.ManyCopies.Stem
open scoped Topology Classical
variable {G:Gauge} {C:Family G}(A:Allot C){V:Type}[Fintype V][DecidableEq V] (P:Ensemble V)
variable {N p k m n j b d:ℕ}{E o:Track C.path V p}
-- certified (not necessarily largest) possible weight paid throughout. decreases by creep at each step. terminal payoff w k. upper threshold j.
structure Line (A:Allot C)(P:Ensemble V)(N p k j b:ℕ)(E o:Track C.path V p) where
   X : Travel C.path V p
   w : ℕ→ℝ
   hold : Run P A.D N p k j E o X w
   guard' : Creep C k b j w
namespace Line
variable {A P}(L:Line A P N p k j b E o)
def damp (a:ℝ)(hz:0<a)(hp:a ≤ 1):Line A P N p k j b E o where
    X:=L.X
    w i := a*L.w i
    hold:=L.hold.credit (fun i ht hk => mul_pos hz (L.hold.fees i ht hk)) (fun i ht hk=>mul_le_of_le_one_left (L.hold.fees i ht.le hk|>.le) hp)
    guard':=L.guard'.scale a hz.le -- dot elaboration?
def cut {i:ℕ} (hk:k ≤ i) (hi:i ≤ j) : Line A P N p k i b E o where
   X:=L.X
   w:=L.w
   hold:= L.hold.crop le_rfl hk hi
   guard':= L.guard'.crop C le_rfl hi
-- combine across seam with matching weights
lemma continueW (S:Line A P N p j m b E o)(hx:L.X j=S.X j)(he:L.w j=S.w j):
    ∃ U:Line A P N p k m b E o, (∀ i,i ≤ j → U.w i=L.w i ∧ U.X i=L.X i) ∧ (∀ i,j ≤ i → U.w i=S.w i ∧ U.X i=S.X i):=by
   let r i:= if i ≤ j then L.w i else S.w i; have hr(i:ℕ)(he:i ≤ j):r i=L.w i:=if_pos he
   have hs(i:ℕ)(hv:j ≤ i):r i=S.w i:=by rcases lt_or_eq_of_le hv with h|rfl; exact if_neg h.not_ge; exact (hr _ le_rfl).trans he
   obtain ⟨X,hX,hU,ho⟩:=Run.seams (L.hold.credit (fun i hK hj=>hr i hj ▸ L.hold.fees i hK hj) (fun i hK hj=>(hr i hj).le)) hx (S.hold.credit (fun i hK hj=>by rw [hs i hK]; exact S.hold.fees i hK hj) (fun i hK hj=>(hs i hK.le).le))
   exact ⟨⟨X,r,hX,Creep.extend (a:=k) (a':=j) (L.guard'.alter (fun i _ hj=> hr i hj)) (S.guard'.alter fun i hi _=>hs i hi)⟩,fun i hi=>⟨hr i hi,hU i hi⟩,fun i hi=> ⟨hs i hi,ho i hi⟩⟩
variable (A P) {v:ℝ}
lemma roll_below (H:C.Makes) (hb:C.ref 0≤ k)(hk:k ≤ j)(hN:j≤N)(hm:Migrating C.path k p j E)(x:ℂ){X:Stem V G (C.S.side j p)}
    (hX: Marked (C.path.rep N p j) (E j) P X)(hp: Blade (C.path.rep N p j) (X.home P.v) (X.oil P.v) (profile (C.path.rep N p j).activities (X.gas P.v)) x (1/(2*v)))
    (hω:v*‖x‖≤1)(hw:0<v)(hW:o j=X.home)(ht:∀ i,k ≤ i → i<j → (C.path.levels.clock.op i p).ratio.parent ∘ o (i+1)=o i):
    ∃ L:Line A P N p k j b E o, L.X j=X ∧ L.w=Run.Below C.path v j:=by
   obtain ⟨PZ,hT,hR,hV,hf⟩:= Run.descenders (A:=C.path) (D:=A.D) (w:=v) H.wilson hk hN hm hX (fun i hi hj=> (A.blades.choose_spec 0).brings i (hb.trans hi) N p _ |>.1) hp hω hw o hW ht
   exact ⟨⟨PZ,_,hR,Creep.below C hw⟩,hT,rfl⟩
end Line
end YM.OPE.Allot
