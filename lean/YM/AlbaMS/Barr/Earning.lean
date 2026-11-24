import YM.AlbaMS.Barr.Exercises
/-!
# Checks all physical inputs now supply records. Connections to Landau options

Any finite lists, at finite regulators. Includes not just local comp field occupiers
with only one A jet; no assumptions for contacts in this exact finite chart claim.
UV/IR removal to justify later as a separate step. Distinct Pole:
The `tree` equalities are ONLY for IdleNot T, this is *after* reset to no
canonical adjustments. Prove conservation for every such registration with same
bare beta. Use for actual perturb comparison. Unconditional constructors given for
Window and history at all finite periods independently. Cost no opportunity calendars.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Barr
open Set Function Filter IsNilpotent LinearMap
open scoped BigOperators Classical Topology Matrix
open Bric Coil Inlay Inlay.Net Odom Token Lattice Nexus Loft Cutis Cutis.Winter
variable {R:Type*}[CommRing R]{V B W J:Type*}[Fintype V][Fintype B][Fintype W][Fintype J]{Ω:Net V B}{H:Net W J}{G:Gauge}

abbrev Pulse (Ω:Net V B)(G:Gauge)(R:Type*):= List (R × Pace Ω G)
namespace Pulse
variable (T:Tune R)(F:Pulse Ω G R)
def sway (T:Tune R)(F:Pulse Ω G R) : Heave G V B R:= (F.map fun x=> x.1 • x.2.rise T).sum
omit [Fintype B] in
lemma lit : EvenT (F.sway T):=by induction F with|nil=>exact Tone.none _
                                                     |cons i l ih=>exact ((Pace.physical T i.2).smul i.1).add ih
def leaf (F:Pulse Ω G R)(Y:Receipt G Ω H):Pulse H G R:=F.map fun x=>(x.1,x.2.lens Y)
omit [Fintype J] in
lemma travel (Y: Receipt G Ω H) : sway T (leaf F Y)= T.crossT Y (sway T F):=by induction F with|nil=> exact (map_zero _).symm|cons i l ih=>
  unfold leaf sway at *; simp only [List.map_cons,List.sum_cons,map_add,map_smul,Pace.replay, ih]
omit [Fintype B] in
lemma ease : SimpleT (sway T F):=by
  induction F with|nil=> exact ⟨Loft.Under.zero, fun _=>map_zero _⟩|cons i l ih=>
   exact ⟨(((i.2.low T).1.smul _).add ih.1),fun j=>by rw [show sway T (i::l)=i.1 • (i.2.rise T)+sway T l from rfl,map_add,map_smul,(i.2.low T).2 j, ih.2 j, smul_zero,add_zero]⟩
lemma closed (P : Odom.Book Ω G) : quantum T.bracket Finset.univ (P.charter T) (sway T F)=0:=by induction F with|nil=>exact map_zero _| cons i l ih=> unfold sway at *; rw [List.map_cons,List.sum_cons, map_add,map_smul,i.2.wall, ih,smul_zero,add_zero]
omit [Fintype B] in
lemma fit (hT:IsNilpotent T.z) : FinRank (sway T F):=by induction F with|nil=>exact FinRank.none|cons i l ih=>exact ((Tune.bounded _ hT).smul _).add ih

-- joint
variable (L: List (Pulse Ω G R))
def holdL (L:List (Pulse Ω G R))(T:Tune R):= (L.map fun F=> sway T F).prod
omit [Fintype B] in
lemma shine : EvenT (holdL L T):=by induction L with|nil=> exact Tone.one|cons i l ih=>exact (lit T i).mul ih
omit [Fintype B] in
lemma radiates (hT:IsNilpotent T.z):FinRank (holdL L T):=by induction L with|nil=>exact FinRank.one|cons i l ih=> exact (fit T i hT).mul ih
omit [Fintype B] in
lemma foam : Loft.SimpleT (holdL L T):=by
  induction L with|nil=>exact ⟨⟨fun _=>D_one ..,fun _=>D_one ..⟩,fun _=>D_one ..⟩|cons i l ih=>
   exact ⟨(ease T i).1.mul ih.1, fun j=> by change D _ (_ * holdL l T) = _; rw [mulD, show D (Place.c j) (sway T i)=0 from (ease T i).2 j, show D (Place.c j) (holdL l T)=0 from ih.2 j]; simp⟩
lemma bodily (Q F: Heave G V B R)(h:Under Q)(H:Under F)(hr: EvenT Q): cross true T.bracket Finset.univ Q F=0:=by change cross true ((T.D (T.a⁻¹))^4 • Loft.oriented R) _ _ _=0; rw [pay_across, show cross true _ _ Q F=0 from Under.free hr h H,smul_zero]
variable [Algebra ℚ R]
lemma pile (P:Odom.Book Ω G): quantum T.bracket Finset.univ (P.charter T) (holdL L T)=0:= by
  let Q:=T.bracket (G:=G) (V:=V) (I:=B); let d:=touch (ρ:=@ø (Flit G V) (Flit G B)) Q Finset.univ; let s:=tether true Q Finset.univ (P.charter T); let D:=quantum Q Finset.univ (P.charter T)
  induction L with
  | nil=>rw [← Salute.bridge]; exact Fritz.part_one _ _ _ -- maybe DecEq not needed?
  | cons x X ih=>
    change s (sway T x*holdL X T)-d (_*_)=_
    let U:=sway T x; let V:=holdL X T
    have hv:s (U*V)= s U* V + U* s V:=by rw [show s (_:Floor _ _ _)=_ from uses T.prime (P.charter_tone T),(lit T x).pl]; rfl -- uses rw target
    have he:d (U*V)= d U* V+ U* d V:=by rw [show d _= _ from main_product_even (p:=true) (lit T x),bodily T _ _ (ease T x).1 (foam T X).1 (lit T x),add_zero] -- pattern
    change s (U*V)-d (U*V)=_; rw [he,hv,show s U=d U from sub_eq_zero.mp (closed T x P), show s V=d V from sub_eq_zero.mp ih,sub_self]
omit [Algebra ℚ R] [Fintype J] in
lemma crew (Y:Receipt G Ω H): T.crossT Y (holdL L T)=holdL (L.map (fun x=> x.leaf Y)) T:=by
  induction L with|nil=>exact shot_put ..| cons i l ih=> change T.crossT Y (sway T i * holdL l T)=sway T (leaf i Y) * holdL _ _; rw [show T.crossT Y _=T.crossT Y (sway T i)*T.crossT Y (holdL l T) from shot_mul .., ← travel, ih]
omit [Algebra ℚ R] [Fintype B] in
lemma truism {U:Tune R} (h: Still T U): holdL L U= weft (lane T U) (holdL L T):=by
  have ho (F:Pulse Ω G R): sway U F=weft (lane T U) (sway T F):=by
    induction F with|nil=> exact (map_zero _).symm | cons i A ih=> unfold sway at *;rw [List.map_cons,List.sum_cons,List.map_cons,List.sum_cons,map_add,map_smul,ih, show i.2.rise U =_ from Still.levels h i.2.k (bare i.2.intent.caseG)]; rfl
  induction L with|nil=>exact (one_on _).symm|cons i X ih=> unfold holdL at *; rw [List.map_cons,List.prod_cons,List.map_cons,List.prod_cons,weft_mul]; exact congr_arg₂ _ (ho i) ih
end Pulse
end YM.MSBar.Barr
