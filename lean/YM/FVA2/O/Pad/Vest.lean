import YM.FVA2.O.Pad.Atom
/-!
# Keep the `4` in $4 + 2k$ constant -- dummy lift for Q-exact generator
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Pad
open MS Function Filter Set Finset MS.Plane MeasureTheory Real Metric
open Momentum Heat Koszul Flux High Landau Detect MS.Color Book Signal Arts Alps MS.Local.Physical
open Wire Spin Pilot Emit Halo
open scoped Topology ContDiff Interval
variable {E:Type} {G:Gauge}{m k n:ℕ}{t b:ℤ}{F:Law G}
local notation "h0"=> Nat.zero_le m
@[simp] lemma accept_none (b:Bool)(i:CI G): accept ( ((none,b),i):Cfield G m )=1:= rfl
@[simp] lemma accept_some (i:L m)(b:Bool)(p:CI G): accept (((some i,b),p):Cfield G m) = cube i:= rfl
lemma turn_low {X:Spin (L m)}(h:X.within false)(p:SectorP m): Cl h0 (X.turn p)=Cl h0 p:= by
    ext i; let j:= rises h0 i; have hh: X.turn (spray j)=spray j:= fixedBasis h0 (h rfl) i; have hz:= X.rad p (spray j); rw [hh] at hz; change X.turn p j=p j; simpa [pairing,Arts.spray, Pi.single_apply,mul_ite] using hz
@[simp] lemma cube_in (i:L 0): cube (rises h0 i)=1:= if_pos i.isLt
@[simp] lemma cube_out (i:Apart 0 m): cube (aside h0 i)=0:= if_neg (not_lt.mpr (Nat.le_add_right ..))
lemma profile_one (x:Spin (L m))(hp:x.within false)(i:L m)(j:L 0): x.profile i (rises h0 j)= if i=rises h0 j then 1 else 0:= by rw [Spin.dual]; unfold profile; rw [fixedBasis h0 ( (within_back _ hp) rfl )]; simp [spray,Pi.single_apply]
lemma mimic (F:Law G)(x:Spin (L m))(hp:x.within false): (flagS x G).beam (bracket F m)=bracket F m:= by
    funext w; unfold flagS; induction w generalizing F with
    | nil=> simp
    | cons i l ih=>
       rcases i with ⟨⟨⟨_|i,b⟩,j⟩,p⟩
       · rw [fromG, from_head,accept_none,one_smul,ih, D_eval _ (bracket F m), from_head,accept_none,one_smul, turn_low hp ]; -- simplify Prod.snd
       rw [ fromV, cut_sum h0 ]; simp_rw [ from_head,map_smul, Pi.smul_apply ]; -- μ
       rw [Finset.sum_eq_zero (s:=Finset.univ) (f:=fun a:Apart 0 m=> _)]; -- too arbitrary? refine.
       swap; · intro i hi; simp
       rw [add_zero]; rcases rangeA i h0 with ⟨a,rfl⟩ | ⟨a,rfl⟩
       · simp_rw [profile_one x hp]; rw [Finset.sum_eq_single a]; case h₀=> intro i hi ht; rw [ if_neg ( (rises h0).injective.ne (Ne.symm ht) ),Complex.ofReal_zero,zero_mul]
         case h₁=> simp
         simp only [ if_true,Complex.ofReal_one,accept_some,cube_in,one_smul,one_mul]; rw [ ih,turn_low hp,D_eval _ (bracket F m), from_head,accept_some,cube_in,one_smul ]
       · simp_rw [profile_one x hp]; rw [Finset.sum_eq_zero]; swap; · intro i hi; rw [if_neg (Ne.symm (nowhere h0 i a)),Complex.ofReal_zero,zero_mul]
         rw [ D_eval _ (bracket F m), from_head ]; simp
lemma roll (x:G.El)(F: Law G)(w: Legs ( Shore G m )): repeatC x (bracket F m) w= bracket (repeatC x F) m w:= by
    induction w generalizing F with
    | nil=> simp [bracket,taxA,floor0, show ∀ (G:Gauge) (u:G.El) (n:ℕ) (X:Rack G n), repeatC u X []=X [] from fun _ _ _ _=>rfl] -- defeq[M]?
    | cons i l ih=> rw [repeat_cons]; simp_rw [from_head,map_smul,Pi.smul_apply,smul_eq_mul,ih]; unfold bracket taxA floor0; rw [ List.map_cons,List.map_cons,List.prod_cons, repeat_cons,Finset.mul_sum ]; refine Finset.sum_congr rfl fun a ha=>?_ ; simp only [setLeg,Prod.map_snd,Prod.map_fst,shrink, Function.comp_apply]; ring_nf -- need rfl
lemma closer (h:m≤n)(p:SectorP m): Cl (Nat.zero_le n) (Left h p)=Cl h0 p:= by ext i; exact lasts (rises h) p (rises h0 i)
lemma shrink_emb (h:m≤n)(i:Cfield G m): shrink (embA (rises h) i)=shrink i:= by rcases i with ⟨⟨_|i,v⟩,s⟩<;> rfl
lemma accept_emb (h:m≤n)(i:Cfield G m): accept (embA (rises h) i)= accept i:= by rcases i with ⟨⟨_|i,v⟩,s⟩<;> rfl
lemma floors_r (F:Law G)(h:m≤n)(l:Legs ( Shore G m )): bracket F n ( lift h l )= bracket F m l:= by induction l generalizing F with| nil=>rfl| cons i l ih=> simp only [ Arts.lift,List.map_cons ]; rw [ D_eval _ (bracket F n), from_head, D_eval _ (bracket F m),from_head ]; simp only [Prod.map_fst,accept_emb,Pi.smul_apply,shrink_emb,Prod.map_snd, closer]; exact congr_arg _ (ih _)
lemma badgeV (X:Law G)(n k:ℕ)(he:X∈ Local.Physical.Lease G (n:ℤ) k b) : Dock.Badge false (fun _=> bracket X) n b:= Pace.prepay ( fun _=> pick (initial_p X n k he) ) ⟨fun _ x hp=> mimic X x hp, fun h=> floors_r X h⟩ (fun m k=> funext fun l=> (roll k X l).trans (congr_fun (congr_fun (congr_arg bracket (((room X b).mp (lease_one.mp he).1).1.color k) ) m) l))
end YM.FVA2.O.Pad
