import YM.WilsonCoeffUV.Horizon.OrbitSpin
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.WilsonCoeffUV.Wheel.Motion
open Wheel.ScaleS Wheel.Mark Function PowerSeries Blue Mer Lattice RG Embroider Embroider.Canvas Soil Bank Laurent Cosmos Filter Gauge Power Matrix Precision Wilson Tree Exterior AnalyticNext.QuarticMatch.Sheets Bloch FreeResolvent Work.F08 Shard Realm PathCost Physical
open Fountain Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Wheel.Flooring Ticket
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {ι:Type}{S:Finset ι}{E W V U:Credit}{m b N e h D' i a:ℕ}{G:Gauge}{A:Levels G}{R:Realm G (e+1) E}{Ñ: ChartRatio G}{T:ι→SealR G}{P:Patch}{n:Side}{σ:Signed}{D K k:ι→ℕ}
variable [DecidableEq ι]
-- all label rotations
abbrev Rings (P:Patch)(σ:Signed): Equiv.Perm (backRow P.L S) := Equiv.piCongrRight fun _=> σ.actEquiv.toEquiv
lemma inflateR (w:backRow P.L S)(i:ι): inflate P S (Rings P σ w) i= σ.act (inflate P S w i):=by unfold inflate; split; rfl; simp
lemma passageR (w:backRow P.L S)(p:ι → Cover): splitQ P (σ.act ∘ p) S (Rings P σ w)= σ.act ∘ splitQ P p S w:=by
    funext i; unfold splitQ copyQ; rw [inflateR,Function.comp_apply,Function.comp_apply,Ratio.lift_signed_of_odd P.odd_side,Signed.act_add]; exact congr_arg₂ (·+·) (Eq.symm (map_nsmul σ.actEquiv _ _)) rfl
lemma braidR (w:backRow P.L S)(U:Case D): swish σ (laid P (inflate P S (Rings P σ w)) U)=laid P (inflate P S w) (swish σ U):=by
   funext i; unfold swish laid; rw [inflateR]; exact Eq.symm (envy ..)

def litSpin (σ:Signed)(X Y:Outerm G D): Prop:=∀ p:ι → Cover,turnsO σ (X p) (Y (σ.act∘p))
lemma mergedSpin {X Y:Outerm G D}(p: Mark.Solo k X)(q: Mark.Solo k Y)(r:litSpin σ X Y): litSpin σ (unite P K X) (unite P K Y):=by
    intro v S n T Z I b F F' u
    rw [stalwart P K Y q, stalwart P K X p,map_sum,map_sum]
    symm; apply Fintype.sum_equiv (Rings P σ); intro j; unfold Mark.streak; rw [train_smul, train_smul, passageR, ← braidR]; exact congr_arg _ (Eq.symm (r (splitQ P v S j) S n _ u))
lemma across {X Y:Outerm G D}(p: Wellness k X)(q: Wellness k Y)(r:litSpin σ X Y)(t:m<N)(g:G.Simple)(f:LocalRatio Ñ): litSpin σ (stout A Ñ m N K k X) (stout A Ñ m N K k Y) :=by
    let Z (X: Outerm G D): Outerm G D:=fun i=> logO A Ñ m N (X i) k; exact mergedSpin (X:=Z X) (Y:=Z Y) (fun i=>step_L _ _ _ _ _ _ t g f (p.level' i)) (fun i=>step_L _ _ _ _ _ _ t g f (q.level' i)) (fun i=> logged (p.level' _) (q.level' _) (p.quiet' _) (q.quiet' _) t g f (r i))
lemma allSpins {X Y: Outerm G D}(p:Wellness k X)(q:Wellness k Y)(r:litSpin σ X Y)(t:m ≤ b)(x:b≤ N)(g:G.Simple)(f:LocalRatio Ñ): litSpin σ (Gears A Ñ K k N b m X) (Gears A Ñ K k N b m Y):=by
    induction t using Nat.decreasingInduction with
    | self=> rw [gearTop,gearTop]; exact r
    | of_succ m h ih=> rw [gearUp A Ñ _ h,gearUp A Ñ _ h]; exact across (Cog A Ñ x X p g f h) (Cog A Ñ x Y q g f h) ih (lt_of_lt_of_le h x) g f
section
variable {H:Hol G}{F: Frame G h}{T':SectionData F}{p':h<D'}
lemma Jacob_spin (L:Theatre H T' p' e E W)(h:L.V.anchor ≤ m)(u:m<N): paintC F σ * Jacob L.V.draws L.V.paid T' p' N m=Jacob L.V.draws L.V.paid T' p' N m * paintC F σ:=by
   let Y:= L.lore N (m+1); let P:=Cosmos.descend L.V.draws L.V.paid N m Y; have hp:= running L.V.draws L.V.paid u L.V.hG L.V.green (production L u (by omega)).1.scan; exact Chain.commutes _ _ hp H p' σ
lemma Names_spin (L:Theatre H T' p' e E W)(t:L.V.anchor≤ m)(p:m+i ≤ N):
   let M:=CurNames L.V.draws L.V.paid T' p' N m i false; paintC F σ * M=M * paintC F σ:=by
   induction i with
   | zero=> simp [CurNames,hillcrest]
   | succ i ih=>
       let C:= Chars F (relativeF L.V.draws L.V.paid N m i); let W':= paintC F σ; have hp:C W'= W':= by ext1 i j; exact reel_C ..
       have hv:= congr_arg C (Jacob_spin (σ:=σ) L (t.trans (show m≤ m+i by omega)) (show m+i<N by omega)); rw [map_mul,map_mul] at hv
       rw [show C (paintC F σ) = _ from hp] at hv; intro M; unfold M; rw [orchestra,←mul_assoc,ih (by omega)]; simp_rw [mul_assoc]; exact congr_arg _ hv
lemma tuneSpin (L:Theatre H T' p' e E W)(t:L.V.anchor≤ m)(p:m+i ≤ N)(X: Verse F) : let K:=paintC F σ; let A:= L.V.draws; let Ñ:=L.V.paid; steep A Ñ T' p' N m i (K*ᵥ X)=K *ᵥ steep A Ñ T' p' N m i X:=by
    obtain ⟨b,v⟩:=ebbing L t p false; intro K A Ñ; unfold steep; rw [v, mulVec_mulVec, irComm _ _ b (Eq.symm (Names_spin L t p)), ← mulVec_mulVec, turnV,show Chars F (relativeC A Ñ N m i) K=K from Matrix.ext (fun i j=> reel_C ..)]
end
end YM.WilsonCoeffUV.Wheel.Motion
