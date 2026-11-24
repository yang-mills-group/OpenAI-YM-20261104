import YM.FormalBulk08.Lotus.Star

noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Shore
open Lava Gorge Lattice Laurent Bloch Filter Set Function Wick Lotus Orb
open scoped BigOperators Classical ENNReal Topology
variable {I J : Type*} [Fintype I] [Fintype J] {r : ℕ}

def cores (R : I→J) (T : Tile I r) : Tile J r:= fun v=> ∑ w:{w:chain I r// R ∘ w=v},T w.val
omit [Fintype J] in
lemma core_sum (R : I→J) (T : Tile I r) (v : chain J r) : cores R T v=∑' w:{w:chain I r//R ∘ w=v},T w.val:= (tsum_fintype (fun w:{w:chain I r//R ∘ w=v}=>T w.val)).symm
lemma pebble (R : I→J) (p : TypeR I) : marble r (MvPolynomial.rename R p)=cores R (marble r p):=by
   let L (i:I) (j:J) : ℝ:=if R i=j then 1 else 0
   have he : MvPolynomial.rename R=mixRows (R:=ℝ) L:= by ext i;simp [L,mixRows,ite_mul]
   rw [he,target]; funext v; unfold pearl cores;rw [tsum_fintype];
   let U:=Finset.univ.filter fun w:chain I r=>R ∘ w=v
   have h (w) (hw:w∈U) (i:Fin r) : L (w i) (v i)=1:= if_pos (congr_fun (Finset.mem_filter.mp hw).2 i)
   rw [←Finset.sum_subset (s₁:=U) (Finset.subset_univ _) (fun w _ hw=>?_)]
   · rw [← Finset.sum_subtype U (p:=fun w=>R ∘ w=v) (fun _=>by simp [U]) (fun w=>marble r p w)]; exact Finset.sum_congr rfl fun w hw=>by simp_rw [h w hw];simp
   · have he : R ∘ w ≠ v:=by simpa [U] using hw
     obtain ⟨i,hi⟩:= Function.ne_iff.mp he;rw [Finset.prod_eq_zero (Finset.mem_univ i) (show L (w i) (v i)=0 from if_neg hi),mul_zero]
omit [Fintype J] in
lemma cores_once (e : I≃J) (T : Tile I r) : cores (e : I→J) T=jetty e.symm T := by
   funext v; unfold cores jetty; let x:{w:chain I r// e ∘ w=v}:=⟨e.symm ∘ v,by ext i; simp⟩
   rw [Finset.sum_eq_single x];
   · intro w _ h;exact False.elim (h (Subtype.ext (funext fun i=>e.injective (congr_fun (w.property.trans x.property.symm) i))))
   simp

variable (m n : Side)
def endo (m n : Side): Ratio m (m*n):= {count:=n,exact_size:=rfl}
def tray : Tor (m*n) I → Tor n I := Prod.map (endo m n).residue id
omit [Fintype I] in
lemma tray_drip (x : Biglot I) : tray m n (drip (m*n) x)=drip n x := Prod.ext (Ratio.residue_wrap _ _) rfl
omit [Fintype I] in
lemma tray_tint (y : Site m) (w : Tor (m*n) I) : tray m n (tint ((endo m n).embed y) w)=tray m n w := by ext <;> simp [tray]

-- representatives holding coarse positions exactly
omit [Fintype I] in
lemma kiln (i : Fin r) (v : chain (Tor n I) r):
    (endo m n).assemble (0,(v i).1) = wrap (m*n) (lift (v i).1) := by rw [Ratio.assemble, ← Ratio.root_embed,map_zero,zero_add];rfl

abbrev Pupil (i : Fin r) (v : chain (Tor n I) r) := {w:chain (Tor (m*n) I) r// tray m n ∘ w=v ∧ w i=drip (m*n) (boil n (v i))}
abbrev Ride (v : chain (Tor n I) r):= {w:chain (Tor (m*n) I) r// tray m n ∘ w=v}

def ghost (i : Fin r) (v : chain (Tor n I) r) (j : Site m × Pupil m n i v) : Ride m n v:=
   ⟨tint ((endo m n).root j.1) ∘ j.2.val,funext fun k=>by rw [comp_apply,comp_apply,Ratio.root_embed,tray_tint]; exact congr_fun j.2.property.1 k⟩
omit [Fintype I] in
lemma ghost_root (i : Fin r) (v : chain (Tor n I) r) (j : Site m × Pupil m n i v) : (ghost m n i v j).val i=((endo m n).assemble (j.1,(v i).1),(v i).2) := by ext <;> simp [ghost,j.2.property.2,Ratio.assemble,boil,drip,endo,add_comm]
omit [Fintype I] in
lemma ghost_bij (i : Fin r) (v : chain (Tor n I) r) : Bijective (ghost m n i v) := by
   let K:=endo m n; constructor
   · rintro ⟨a,x⟩ ⟨b,y⟩ h; have he:=congr_fun (congr_arg Subtype.val h) i; rw [ghost_root,ghost_root] at he
     have hx : a=b:= congr_arg Prod.fst (K.assemble_bijective.1 (congr_arg Prod.fst he)); subst b
     rw [show x=y from Subtype.ext (funext fun j=> (tint (K.root a) (I:=I)).injective (congr_fun (congr_arg Subtype.val h) j))]
   intro w; have he : tray m n (w.val i)= v i:=congr_fun w.property i
   let y:=K.parent (w.val i).1
   have hT : tint (K.root y) (drip (m*n) (boil n (v i)))= w.val i := by
      apply Prod.ext
      ·
        rw [tint_fst, add_comm]; have hh : K.residue (w.val i).1 = (v i).1:= (show ((tray m n) (w.val i)).1=_ from congr_arg Prod.fst he)
        have ht:=K.unpack_at (w.val i).1; rw [hh] at ht; exact ht
      change (v i).2= (tray m n (w.val i)).2; exact congr_arg Prod.snd he.symm
   let z : chain (Tor (m*n) I) r:=(tint (K.root y)).symm ∘ w.val; have hw : tint (K.root y) ∘ z=w.val:= funext fun j=> Equiv.apply_symm_apply ..
   have hz : tray m n ∘ z=v:=funext fun j=>by have hx:tray m n (tint (K.root y) (z j))=tray m n (z j):= tray_tint m n y (z j); change tray m n _ = _; rw [←hx,show tint (K.root y) (z j)=_ from congr_fun hw j];exact congr_fun w.property j
   have hh : z i=_ := (tint (K.root y) (I:=I)).injective ((congr_fun hw i).trans hT.symm)
   exact ⟨(y,⟨z,hz,hh⟩),Subtype.ext hw⟩
lemma core_tally (i : Fin r) (v : chain (Tor n I) r) {T : Tile (Tor (m*n) I) r} (h : Up T) : cores (tray m n) T v = Fintype.card (Site m) * ∑ j:Pupil m n i v,T j.val := by
   rw [core_sum]; let E:= Equiv.ofBijective _ (ghost_bij (I:=I) m n i v); change (∑' w:Ride m n v,T w.val)=_
   rw [←Equiv.tsum_eq E,tsum_fintype]
   rw [Fintype.sum_prod_type]
   have ht (x : Site m) (w : Pupil m n i v) : T (ghost m n i v (x,w)).val=T w.val:= h _ _
   simp only [E,Equiv.ofBijective_apply,ht,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
end YM.FormalBulk08.Shore
