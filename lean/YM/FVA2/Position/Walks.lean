import YM.FVA2.Position.Slew
/-!
# H symmetry in the MS kernel implementation on the lattice

Use the stipulated net-sector restrictions in the `PC`/`PM` parameters (see e.g.
`saturated`). Keep orientation even before evaluating the mark kernels. This is the `Signed` action
used on `Cover` stencils as well. Keep the right-beam convention.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Position.Crosswind
open Function Set Filter Finset MeasureTheory Lattice
open MS MS.Plane MS.Tone MS.Koszul MS.Heat MS.Book MS.Landau MS.Landau.Detect MS.Momentum MS.Plane.Wire
open MS.Native MS.Native.Wilsonian MS.City MS.Tone.Frame MS.Arts MS.Arts.Spin MS.Outlook MS.Color
open Brass
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace Classical
variable {m n:ℕ} {J:Type} {G:Gauge}{v u:ℤ} {K L: Law G}
variable (s:Signed)
abbrev α (s:Signed) : Law G →ₗ[ℂ] Law G:= (flagS (m:=0) ( hand s ) G).beam
local notation "V"=> α s
lemma βfront (a:BH G) : (passN s a)= toward (m:=0) s a:= by rcases a with ⟨⟨_|i,b⟩,c⟩; rfl; refine Prod.ext ?_ rfl; exact Prod.ext (congr_arg Option.some (Eq.symm (ahead s (n:=0) i))) rfl
lemma βcost (a:BH G): tick s a=( tt (m:=0) s a :ℂ ) := by
  rcases a with ⟨⟨_|i,b⟩,c⟩
  · simp [tt,tick,negateField]
  unfold tick negateField tt; rw [Option.elim_some,show Brass.mark s (n:=0) i=sig s i from amark s i]; unfold sig; cases he:s.flip i <;> simp [he]
lemma αcash (F: Law G): V F = cash s 0 F:= by rw [Brass.cash,viewD,Weft.selfA]
lemma αlamp (i: BH G)(p: QP): permute s (i,p)=torso (m:=0) s ( i,p ):= by rw [ City.passenger ]; unfold torso; rw [βfront,viewD,Weft.selfA]; rfl
lemma provs (a b:BH G): ( flagS (m:=0) (hand s) G ).fieldC a b= if a=(passN s).symm b then tick s a else 0:= by
   rw [show (hand s)=viewD s 0 from (Weft.selfA (m:=0) (hand s)).symm,show (flagS (viewD s 0) G).fieldC a b= _ from area ( m:=0 ) s a b, ← βfront, βcost]; split_ifs <;> ( first | rfl | (rename_i hu hv; exact False.elim <| hv ((passN s).symm_apply_eq.mpr hu).symm)| (rename_i hu hv; exact False.elim (hu (((passN s).symm_apply_eq).mp hv.symm))) )
-- winding lattice
lemma enroll (x:Cover): s.act ( Tone.rep x )= Tone.rep (s.act x):= by change ( hand s ).turn ((2*Real.pi) • embed x)= _; rw [map_smul]; exact congr_arg (((2*Real.pi):ℝ) • ·) (emb_H s x)
lemma heel (a:Axis): s.act (embed (Lattice.step a))= sig s a • embed ( Lattice.step (s.perm a)):= by rw [emb_H, MS.Native.Orient.stepflip]; cases he:s.flip a <;> simp [he,sig,emb_neg]
lemma sailsH (x:Cover)(a:BH G): veil (s.act x) (passN s a)=veil x a:= by
    unfold veil; rw [ ← enroll ]; rcases a with ⟨⟨_|i,b⟩,c⟩; · rw [show offset ((passN s) ((none,b), c)).1=0 from here_b b, here_b,right0,right0]
    rw [ show ((passN s) _).1=(some (s.perm i),b) from rfl,here_a, here_a ]; let U i:= (1/2:ℝ) • embed (Lattice.step i); have hK : s.act (U i)= sig s i • U (s.perm i):= by unfold U; rw [show s.act ((1/2:ℝ) • _)=_ from map_smul ( hand s ).turn (1/2:ℝ) ( embed (Lattice.step i) ), show (hand s).turn (embed (Lattice.step i))=_ from heel s i, smul_comm]
    change bill _ (U _) = bill _ (U _); cases he:s.flip i
    · rw [show U (s.perm i)= s.act (U i) from by simpa only [sig,he,Bool.false_eq_true,↓reduceIte,one_smul] using hK.symm, turnC ]
    rw [show U (s.perm i) = s.act (-(U i)) from ?_,turnC, Tone.inverse ]; exact inv_eq_of_mul_eq_one_right (testv x i b); rw [Signed.act_neg,hK,sig,he,if_pos rfl,neg_one_smul,neg_neg]
lemma marches_h (h:Perk K): Perk (V K):= by
 intro l r i p q; rw [show V K (l++_::_)= _ from hand_index s (l++(i,p+rep q)::r) K,show V K (l++_::_)= _ from hand_index s (l++(i,p)::r) K ]; simp only [List.map_append,List.map_cons,passenger,Signed.act_add,enroll,List.prod_append, List.prod_cons,tick1, h _ _ _ _ _, sailsH]; ring
-- precise pass Lap tree (unmarked only restricted before tree)
abbrev pilot (s:Signed)(G:Gauge) := flagS (m:=0) ( hand s ) G
lemma drives (G:Gauge)(p:ℝ): Pilot.Transport (pilot s G) (Cpu G p) (Cpu G p):= by
 intro x a b; let A:=passN (G:=G) s; obtain ⟨a,rfl⟩:= A.surjective a; obtain ⟨b,rfl⟩:= A.surjective b; unfold pilot A; simp_rw [ provs, Equiv.symm_apply_apply,mul_ite,mul_zero ]; rw [show (flagS (m:=0) (hand s) G).volp x= s.act x from rfl,turn_p]; simp; ring
lemma bus (G:Gauge): MeasurePreserving (pilot s G).volp μzone μzone:= measureVeh s
open MS.Wind
-- `viewport Smooth` multilinear.Hiq
lemma slopeW {K:Flow G}(h:TouchF K): TouchF (V ∘ K):= by
    intro E _ _ f w hw hf; let r: tagSmooth E ( BH G ) QP:= w.map fun i=> (passN s i.1, ((hand s).turn) ∘ i.2 ); have ht : Trail r:= by intro j hj; obtain ⟨j,ht,rfl⟩:=List.mem_map.mp hj; exact (hand s).turn.contDiff.comp (hw j ht)
    simp only [Function.comp_apply, α]; rw [ show (fun p:E=> (flagS (m:=0) ( hand s ) G).beam ( K ( f p ) ) (walk0 w p))=(fun p=> ( ( walk0 w 0 ).map (negateField s)).prod * K ( f p ) (walk0 r p)) from ?_ ]; exact ContDiff.mul contDiff_const (h E f r ht hf)
    funext p; rw [hand_index]; unfold r walk0; simp_rw [List.map_map]; congr 1 
lemma primary (t:ℝ)(F:Flow G)(h:TouchF F): V (Wiref G F t)= Wiref G (V ∘ F) t:= by
    change V (orbit _ _ (F t)) = orbit _ _ ((V ∘ F) t); rw [ finite_cc μzone (period0 μzone cour0 (main_f G) h), finite_cc μzone (period0 μzone cour0 ( main_f G ) (slopeW s h)) ]; exact Pilot.leadC (pilot s G) (bus s G) (Homeomorph.measurableEmbedding (hand s).turn.toHomeomorph ) (drives s G t) (F t) (period0 μzone cour0 (main_f G) h )
lemma preset (h:SignedScope true K): translate (V K)= Plane.translate K := by
    refine agree_trans.mp ?_; intro l hl; unfold α; rw [hand_index]; exact h s l (fun _=>hl)
lemma primaryQ (t:ℝ)(F: Law G)(h:SignedScope true F)(L:Law G): V (boulevard parity ( Cpu G t ) F L )= boulevard parity ( Cpu G t ) F (V L) := by
    simp only [blvd]; rw [ show V ( Flux.tree parity (Cpu G t) F L ) = _ from Pilot.Transport.gatherR ( drives s G t ) F L (City.X_even G t) (City.X_even G t) ]; rw [← tree_trans (F:=V F), preset s h, tree_trans] -- shadow
lemma xLimit (h:Limit K v): Limit (V K) v:= by
 intro w hw; rw [α,hand_index, h, mul_zero]; simpa
lemma melody (h:Symm (field parity) K) : Symm (field parity) (V K):= by
 intro l i j r; rw [α, hand_index, hand_index ]; simp only [ List.map_append,List.map_cons,List.prod_append,List.prod_cons,h _ (permute s i) (permute s j), City.back_p ]; ring
lemma reflection (h:World K): World (V K):= by
 intro w; rw [ αcash s K, Brass.evaluate s (m:=0) K, Brass.evaluate s (m:=0) K, (Park.rear_s (m:=0) s w).2, (Park.rear_s s (m:=0) w).1,h,star_mul']; simp
lemma solid (h:wins K v): wins (V K) v:= by
 intro w hw; rw [αcash s K, Brass.evaluate s (m:=0) K,h (Brass.rack (m:=0) s w) (( (Park.hair_h (m:=0) s w) |>.symm ▸ (show Garment.hair (m:=0) w≠v from hw)) : (Garment.hair (m:=0) (Brass.rack (m:=0) s w)) ≠ v ), mul_zero]
lemma βpaid {F:Flow G} (h: Bon false u F): Bon false u (V ∘ F) where
 stand t h:= by cases h
 t_color t q:= by change repeatC q (V (F t))=_; rw [αcash,  show repeatC q _= _ from Park.pace_t s (m:=0) q (F t), h.t_color t q, ← αcash]; rfl
 perk _:= marches_h s (h.perk _)
 real _:= reflection s (h.real _)
 sym _:= melody s (h.sym _)
 pulse _:= solid s (h.pulse _)
 joint:= slopeW s h.joint
abbrev βK : Flow G→ₗ[ℝ] Flow G := LinearMap.pi fun x:ℝ=> ((α s).restrictScalars ℝ).comp ( LinearMap.proj x )
lemma βfund {F:Pack G}(h:Fees false u F): Fees false u (fun x=> α s ∘ F x) := by
    obtain ⟨v,H⟩:= h.pay; exact ⟨fun x=> βpaid s (h.stay x),⟨v,fun i t=>xLimit s ( H i t )⟩, h.currency.linear (βK s) ⟩
-- rotate Cover symbol. Orientation push uses right-beam inverse explicitly.
lemma narrated (F:Dot G Cover): Tone.run (Orient.pose s F)=α s⁻¹ (Tone.run F) := by
  have he : α s (Tone.run (Orient.pose s F))=Tone.run F:= by
      ext l; unfold α; rw [ hand_index,Tone.by_shift,← mul_assoc,City.twice_S,one_mul ]
  rw [← he]; unfold α; rw [handInv]; exact Eq.symm ( Weft.beam_inv' (m:=0) _ _ )
open MS.Book.Program MS.Logarithm
lemma saturated {p:Team}{F H:Dec G}{φ:Actor G}(h:PC G p F)(he:PM φ F H v): PM (fun x=> Orient.pose s ∘ φ x ) F (fun i t=> α s⁻¹ ∘ H i t) v := by
    let L(x:ℝ)(F:Actor G):= φ x; refine ⟨fun i=> βfund s⁻¹ (he.owes i),?_⟩; let U(i:ℕ)(t:ℝ): Flow G:= α s⁻¹ ∘ H i t; intro i x; have hb:=he.recu i x
    refine ⟨?_,?_⟩; · rw [comp_apply,comp_apply,narrated,hb.1]
    intro t l; -- derivative with phase; pay Sat
    have ht : path 1 i 0 F U x t=α s⁻¹ (path 1 i 0 F H x t):= by
        unfold path; rw [one_smul,one_smul]; simp_rw [Finset.sum_apply,map_sum]; apply Finset.sum_congr rfl; intro j hj; exact (primaryQ s⁻¹ t _ ((( h.owes _ ).stay x).stand t rfl) _).symm
    rw [ ← primary s⁻¹ t (H i x) ((he.owes i |>.stay x).joint) ]; change HasDerivAt (fun t=> α s⁻¹ ( H i x t ) l) ( ( α s⁻¹ (Wiref G ( H i x ) t)+ (path 1 i 0 F U x t) ) l) t; rw [ht, ← map_add]; simp_rw [show ∀ (T:Law G), α s⁻¹ T l= _ from fun T=> hand_index s⁻¹ l T ]; exact (hb.2 t ( l.map ( permute s⁻¹ ))).const_mul _
end YM.FVA2.Position.Crosswind
