"""The seven stories.  Single source for gallery/index.html and STORIES.md.

Inline markup is limited to <i>, <b>, <sub>, <sup>.  Every number here is
taken from hi_cft_c8_proof.tex, its \\input physics sections, or the
c8_physics_20260927 datasets; section numbers follow hi_cft_c8_proof.aux.
"""

INTRO = dict(
    kicker='A gallery from the central-charge-eight Haagerup construction',
    title='Seven Views of Haagerup',
    dek=('A conformal field theory with Haagerup symmetry, seen seven ways. Every image is drawn '
         'from exact data in the construction. The story under each one says what you are '
         'looking at and where it enters the work.'),
    status=('The manuscript is a research draft. Its realization statements rest on explicit '
            'finite certificates recorded in its ledger. Exact replays check those identities, '
            'and no machine verification of the whole construction is claimed.'),
)

VIEWS = [
    dict(
        slug='symmetry', img='r1_fusion_graph', accent='teal',
        kicker='The symmetry',
        title='A symmetry with an irrational size',
        dek=('The Haagerup category has six members. Three of them act like the rotations of a '
             'triangle. The other three each have size (3 + √13)/2.'),
        alt=('Three large glass spheres glowing teal, each circled by a thin ring, joined in a '
             'triangle by arcs of light; each has a small gold sphere attached on a gold thread.'),
        body=[
            ('Ordinary symmetries form groups. Do two of them and you get a third, and every one '
             'can be undone. The Haagerup fusion category, which grew out of a subfactor that Uffe '
             'Haagerup identified in the early 1990s, has six simple objects that combine differently. Three of '
             'them, 1, <i>α</i> and <i>α</i><sup>2</sup>, compose like the rotations of a '
             'triangle, with <i>α</i><sup>3</sup> = 1. The other three obey '
             '<i>ρ</i> ⊗ <i>ρ</i> = 1 ⊕ <i>ρ</i> ⊕ <i>αρ</i> ⊕ <i>α</i><sup>2</sup><i>ρ</i>. '
             'Combining <i>ρ</i> with itself produces four objects at once, and nothing undoes it.'),
            ('Each object has a size, its quantum dimension. Sizes multiply under ⊗ and add under '
             '⊕, so the rule for <i>ρ</i> forces <i>d</i><sup>2</sup> = 1 + 3<i>d</i>, and '
             '<i>d</i> = (3 + √13)/2 ≈ 3.303. A group element always has size one. That is why '
             'this symmetry does not fit inside any group, and why it has been hard to find in '
             'quantum field theory.'),
            ('In the render each object is a sphere. A line joins two objects when one of them '
             'appears in <i>ρ</i> times the other. The sizes are not chosen by hand: they are the '
             'Perron–Frobenius eigenvector of this graph, and its eigenvalue is <i>d</i>. The '
             'ring around each teal sphere is a self-loop. It records that <i>ρ</i> occurs inside '
             '<i>ρ</i> ⊗ <i>ρ</i>.'),
            ('In the manuscript these objects become topological lines in a unitary conformal '
             'field theory at <i>c</i> = 8. The chosen <i>E</i><sub>8</sub> extension of the '
             'chiral algebra carries them, and a line can be wrapped around space and read as an '
             'operator. The line <i>ρ</i> multiplies the vacuum sector by <i>d</i> and the next '
             'sector, <i>b</i>, by −1/<i>d</i>.'),
        ],
        see=[
            'Sphere radius is proportional to quantum dimension: 1 for the gold spheres (1, <i>α</i>, <i>α</i><sup>2</sup>) and <i>d</i> ≈ 3.303 for the teal ones (<i>ρ</i>, <i>αρ</i>, <i>α</i><sup>2</sup><i>ρ</i>).',
            'Edges: <i>x</i> is joined to <i>y</i> when <i>y</i> occurs in <i>ρ</i> ⊗ <i>x</i>. So 1–<i>ρ</i>, <i>α</i>–<i>α</i><sup>2</sup><i>ρ</i>, <i>α</i><sup>2</sup>–<i>αρ</i>, and every pair of teal spheres, including each with itself (the rings).',
            'Blender Cycles render: glass spheres with glowing cores on a fading lacquer floor.',
        ],
        work=('Theorem 1.4, VOA realization and holomorphic extension (p. 6). Section 6, the '
              'Haagerup symmetry of the holomorphic extension (p. 23): the line actions and the '
              'twined trace Z<sup>[ρ]</sup> = (<i>d</i>χ<sub>0</sub> − <i>d</i><sup>−1</sup>χ<sub><i>b</i></sub>)'
              '<span class="ov">χ</span><sub><i>E</i><sub>8</sub></sub>, eq. (73).'),
    ),
    dict(
        slug='e8', img='r2_e8_248', accent='gold',
        kicker='The hiding place',
        title='Hiding inside E<sub>8</sub>',
        dek=('The theory is built inside the most symmetric lattice in eight dimensions. Its '
             '248 currents split three ways, and whether two of the parts agree decided the '
             'shape of the whole construction.'),
        alt=('A mandala of 240 glowing dots in gold, teal and coral on eight concentric rings, '
             'webbed with thousands of faint lines; sixteen gold dots are circled in white and a '
             'small octagon of white light sits at the center.'),
        body=[
            ('The <i>E</i><sub>8</sub> lattice gives a conformal field theory at central charge 8 '
             'with 248 conserved currents: eight along the Cartan directions and one for each of '
             'the 240 roots drawn here. The picture is the classic projection in which the roots '
             'fall on eight rings of thirty.'),
            ('The construction starts one step down, in the sublattice <i>E</i><sub>6</sub> ⊕ '
             '<i>A</i><sub>2</sub> of index three. Its 78 roots are gold. The rest of '
             '<i>E</i><sub>8</sub> splits into two cosets of 81 roots each, teal and coral. From '
             'the gold part the manuscript picks six currents, an sl<sub>2</sub> at level 1 and an '
             'sl<sub>2</sub> at level 39, whose roots are ringed in white. With the stress tensor '
             'and one more field <i>u</i> they generate the chiral algebra <i>U</i>.'),
            ('Seen from <i>U</i>, the 248 currents regroup as 6 + 80 + 81 + 81. The 6 belong to '
             '<i>U</i>. The 80 fill out the rest of the gold part. The teal and coral 81s start two '
             'sectors, <i>Y</i> and <i>Y</i>*.'),
            ('The proof then turns on a yes-or-no question. Are <i>Y</i> and <i>Y</i>* the same? '
             'If they differ, the symmetry left over has four objects. If they agree, it has six. '
             'The manuscript rules out four, so teal and coral carry the same sector. Further '
             'arguments identify the six-object ring as Haagerup, and the chosen '
             '<i>E</i><sub>8</sub> extension restricts to <i>U</i> as <i>M</i><sub>0</sub> ⊕ '
             '<i>M</i><sub><i>b</i></sub> ⊕ 2<i>M</i><sub><i>a</i></sub>.'),
        ],
        see=[
            'All 240 roots of <i>E</i><sub>8</sub>, computed from the manuscript\'s own <i>E</i><sub>6</sub> ⊕ <i>A</i><sub>2</sub> Gram matrix and projected to the Coxeter plane (8 rings × 30).',
            'Colour is the ℤ<sub>3</sub> coset: 78 gold (<i>E</i><sub>6</sub> ⊕ <i>A</i><sub>2</sub>), 81 teal, 81 coral. The 6,720 edges join roots at 60° and are drawn as additive light.',
            'White rings: the 16 roots ±<i>α</i><sub><i>L</i></sub> and ±<i>α</i><sub><i>i</i></sub> (<i>c</i><sub><i>i</i></sub> ≠ 0) used by <i>U</i>\'s six currents. Centre: the 8 Cartan directions.',
        ],
        work=('Appendix A and Lemma A.1, the lattice and the two affine levels (pp. 28–29). '
              'Section G.1, eqs. (112)–(113): <i>B</i>↓<i>U</i> = <i>U</i> ⊕ <i>X</i> and '
              '<i>H</i>↓<i>U</i> = 1 ⊕ <i>X</i> ⊕ <i>Y</i> ⊕ <i>Y</i>*. Section G.2, eq. (114): the '
              'rank-four or rank-six fork. Section G.3: excluding rank four (p. 48).'),
    ),
    dict(
        slug='seed', img='r3_seed_field', accent='coral',
        kicker='The seed',
        title='One field, three waves',
        dek=('Six currents and one extra field generate the whole theory. The field is a sum of '
             'three waves, and the arithmetic fact 13 + 27 = 40 fixes the phase between them.'),
        alt=('A honeycomb interference pattern in gold, coral, violet and teal, fading in from '
             'the left, where a unit circle shows three arrows labelled 1, zeta and zeta bar and a '
             'right triangle with sides root 13, 3 root 3 and root 40.'),
        body=[
            ('A lattice theory is built from waves. Each lattice vector <i>a</i> gives a field '
             'e<sup><i>a</i></sup> that behaves like a plane wave with momentum <i>a</i>. The '
             'defining field of the construction adds three of them: '
             '<i>u</i> = e<sup><i>a</i><sub>1</sub></sup> + ((√13 + 3√−3)/20) '
             'e<sup><i>a</i><sub>2</sub></sup> + ((√13 − 3√−3)/20) e<sup><i>a</i><sub>3</sub></sup>.'),
            ('Each momentum has squared length 4, and each pair meets at 60°. Together with the '
             'origin they form a regular tetrahedron. Measured from their centre, they are three '
             'wave vectors 120° apart. Three such waves interfere in a honeycomb. At the dark '
             'points the waves cancel, and the phase, shown as colour, winds once around each '
             'of them.'),
            ('In the theory\'s positive inner product the three coefficients become 1, ζ and '
             '<span class="ov">ζ</span>, with ζ = (√13 + 3<i>i</i>√3)/√40. Its length is exactly '
             '1 because 13 + 27 = 40. So there is no dial left to turn. The field carries both '
             'signature numbers of the theory, √13 from the Haagerup dimension and √−3 from the '
             'triangle of invertible objects. Its charges under the two current algebras are 1 '
             'and 13.'),
            ('Everything else is computed inside the lattice theory. <i>U</i> has 6 states of '
             'weight one, 120 of weight two and 956 of weight three. The hard part of the proof is '
             'showing that <i>U</i> is proper: that no singular product of its higher fields ever '
             'creates a new current, at any weight. A finite strong-generation criterion settles '
             'this using exact identities over ℚ(√13, √−3).'),
        ],
        see=[
            'Brightness: |<i>f</i>|<sup>2</sup>/9 for <i>f</i>(<i>x</i>) = e<sup><i>ik</i><sub>1</sub>·<i>x</i></sup> + ζ e<sup><i>ik</i><sub>2</sub>·<i>x</i></sup> + <span class="ov">ζ</span> e<sup><i>ik</i><sub>3</sub>·<i>x</i></sup>, the classical profile of <i>u</i> on the plane its momenta span. Colour: arg <i>f</i>. Thin white lines: the phase in steps of π/3.',
            'The three phases multiply to 1, so the pattern is a translate of the one for equal phases. The invariant content is in the phasor diagram on the left.',
            'Left: the unit circle with 1, ζ and <span class="ov">ζ</span>, and the right triangle √13, 3√3, √40 scaled by 1/√40.',
        ],
        work=('Eq. (83), the defining field, and its positive transport (Appendix A, p. 29). '
              'Certificate A.2, the constructed spaces in weights two and three (p. 30). '
              'Proposition 1.1 and Appendices B–E, strong generation and properness in all weights.'),
    ),
    dict(
        slug='core', img='r4_five_squared', accent='coral',
        kicker='The core',
        title='Five squared is minus one',
        dek=('Deep inside the algebra sits a core glued from two well-known theories. The glue '
             'exists because 5 × 5 = 25 is one less than 2 × 13.'),
        alt=('A dark torus covered by a 13 by 13 grid of faint points; a bright coral curve winds '
             'once around it the long way and five times around the tube, through thirteen coral '
             'beads, crossing a faint violet curve at a single gold point in front.'),
        body=[
            ('To control every module of <i>U</i> at once, the proof looks for a smaller algebra '
             'inside it that is already understood. It finds one made of two pieces: a '
             'lattice–Potts core of central charge 14/5, and the level-13 parafermions of '
             'central charge 8/5. Each piece has simple currents labelled by residues mod 13. '
             'Together their labels (<i>j</i>, <i>k</i>) fill the 13 × 13 grid on this torus.'),
            ('Two such currents can be glued into a larger algebra only if the combined spin is a '
             'whole number. For the label (<i>j</i>, <i>k</i>) the spin is '
             '−(<i>j</i><sup>2</sup> + <i>k</i><sup>2</sup>)/13 up to integers, so gluing needs '
             '<i>j</i><sup>2</sup> + <i>k</i><sup>2</sup> divisible by 13. Because '
             '5<sup>2</sup> = 25 ≡ −1 (mod 13), the solutions are exactly the lines '
             '<i>k</i> = −5<i>j</i> and <i>k</i> = 5<i>j</i>. On the torus each line becomes a knot '
             'that goes once around the long way and five times around the tube.'),
            ('The two lines cannot both be used, because together they generate labels with '
             'fractional spin. An exact field certificate supplies weight-two vectors in <i>U</i> '
             'with charge (5, 1), which lies on the coral line <i>k</i> = −5<i>j</i>. With the '
             'manuscript\'s orientation convention, that is the line realized. The result is '
             'a subalgebra whose representation category is Fib ⊠ SO(3)<sub>13</sub>, with '
             'fourteen simple modules.'),
            ('This core is what bounds the lowest weight of every <i>U</i>-module by 17/10, '
             'without assuming unitarity. That bound is the first step in pinning down all '
             'twelve sectors. The final lowest weights top out at 15/13.'),
        ],
        see=[
            'The 169 labels (<i>j</i>, <i>k</i>) ∈ (ℤ/13)<sup>2</sup> placed on a torus. Coral: the isotropic line <i>k</i> = −5<i>j</i> (13 beads) and the continuous (1, −5) torus knot through them.',
            'Violet: the other isotropic line <i>k</i> = 5<i>j</i>, which cannot also occur. Gold: the vacuum (0, 0), the only label on both lines.',
            'Faint grid: the 13 + 13 coordinate circles. Blender Cycles render.',
        ],
        work=('Section G.1, a universal top bound and actual lattice branching (pp. 44–46): the '
              'order-thirteen gluing, Rep(<i>A</i><sub><i>L</i></sub>) ≃ Fib ⊠ SO(3)<sub>13</sub>, '
              'and the bound 0 ≤ <i>h</i> ≤ 17/10 in eq. (111).'),
    ),
    dict(
        slug='clock', img='r5_thirteen_hours', accent='violet',
        kicker='The fingerprint',
        title='Thirteen hours',
        dek=('The theory has twelve kinds of particle. On a clock with thirteen hours, six of them '
             'sit exactly on the hours that are not perfect squares.'),
        alt=('Left, a clock face with thirteen hours: six coral beads on the rim, hollow circles '
             'at the other hours, two violet beads on an inner ring and four gold beads in the '
             'centre. Right, a zigzag path of twelve teal and coral arrows ending on a gold ring '
             'labelled root 13.'),
        body=[
            ('A rational conformal field theory sorts its states into finitely many sectors. Here '
             'there are twelve, the simple objects of the Drinfeld center <i>Z</i>(<i>H</i><sub>3</sub>). '
             'Each has a twist, a phase set by its conformal weight. On a 13-hour clock the six '
             'sectors <i>d</i><sub>1</sub>, …, <i>d</i><sub>6</sub> land at hours 6, 11, 2, 5, 7 '
             'and 8. These are exactly the non-squares mod 13. The squares 1, 3, 4, 9, 10 and 12 '
             'are the empty sockets. Two more sectors sit on a three-hour dial inside, and four '
             'with trivial twist sit at the centre.'),
            ('Squares and non-squares mod 13 are the ingredients of a Gauss sum. Take twelve unit '
             'steps, the <i>j</i>-th in the direction of hour <i>j</i>: forwards if <i>j</i> is a '
             'square, backwards if not. The coral steps are the backward ones, at the same hours '
             'as the coral beads. The walk ends exactly at √13. The manuscript\'s defect code '
             'builds √13 this way. It then checks the modular data in exact arithmetic over '
             'ℚ(ζ<sub>13</sub>): <i>S</i><sup>2</sup> = 1, (<i>S</i>Θ)<sup>3</sup> = 1, and all '
             '1,728 fusion coefficients are non-negative integers.'),
            ('The clock also fixes the characters. The modular data allow a family of character '
             'vectors, built from Evans and Gannon\'s fundamental matrix and indexed by an integer '
             'γ ≥ 0, and the member γ has 6 + 13γ currents. The construction has exactly six, so '
             'γ = 0, and the whole vector follows. The vacuum character begins '
             '<i>q</i><sup>−1/3</sup>(1 + 6<i>q</i> + 120<i>q</i><sup>2</sup> + 956<i>q</i><sup>3</sup> + 6010<i>q</i><sup>4</sup> + ⋯).'),
            ('One subtlety: the twist of <i>d</i><sub>3</sub> points to hour 2, but its lowest '
             'weight is 15/13, not 2/13. The clock shows only the phase; the weight goes one full '
             'turn further.'),
        ],
        see=[
            'Outer dial: sector <i>d</i><sub><i>j</i></sub> at hour 6<i>j</i><sup>2</sup> mod 13, read off its twist e<sup>2π<i>i</i>·6<i>j</i><sup>2</sup>/13</sup>. Hollow sockets: the quadratic residues.',
            'Inner dial: <i>c</i><sub>1</sub> and <i>c</i><sub>2</sub> at twists e<sup>2π<i>i</i>/3</sup> and e<sup>4π<i>i</i>/3</sup>. Centre: 0, <i>b</i>, <i>a</i>, <i>c</i><sub>0</sub> with twist 1.',
            'Bead area is proportional to quantum dimension: 1, <i>d</i><sup>2</sup> ≈ 10.9, <i>s</i> = 2 + 3<i>d</i> ≈ 11.9, 3<i>d</i> ≈ 9.9. Right: partial sums of Σ (<i>j</i>/13) e<sup>2π<i>ij</i>/13</sup>, with (<i>j</i>/13) the Legendre symbol.',
        ],
        work=('Section 5, modular data, topological defects and conformal boundaries (p. 20), with '
              '<span class="mono">c8_physics_20260927/defects.py</span>. Appendix H and Lemma H.1, '
              'the complete character vector and γ = 0 (p. 58).'),
    ),
    dict(
        slug='correlator', img='r6_correlator_landscape', accent='teal',
        kicker='The interaction',
        title='The shape of a four-point function',
        dek=('Modular data say which particles exist. Correlators say how they interact. This is '
             'the first exact one, drawn as a landscape.'),
        alt=('A glowing terrain striped with gold, coral, violet and teal and traced with '
             'contour lines; two volcano-like peaks with gold calderas rise side by side, and a '
             'teal sinkhole opens in the foreground.'),
        body=[
            ('Place the field <i>u</i> and its conjugate at 0, <i>x</i>, 1 and infinity. The '
             'four-point function is then an exact rational function, '
             '<i>G</i><sub>0</sub>(<i>x</i>) = (3 − 4<i>x</i> + 4<i>x</i><sup>2</sup>) / '
             '(3<i>x</i><sup>4</sup>(1 − <i>x</i>)<sup>4</sup>). Each field is a sum of three '
             'exponentials, so the product has 81 terms. Charge conservation kills all but 15, '
             'and each survivor carries weight 1/9.'),
            ('The landscape shows its size as height, on a log scale, and its phase as colour, '
             'over the complex <i>x</i>-plane. Where two operators collide, at <i>x</i> = 0 and '
             '<i>x</i> = 1, there are poles of order four. They rise as glowing calderas, and the '
             'colours wind four times around each. The two sinkholes at <i>x</i> = ½ ± '
             '<i>i</i>/√2 are the zeros. The mirror symmetry across Re <i>x</i> = ½ is crossing '
             'symmetry, <i>G</i><sub>0</sub>(1 − <i>x</i>) = <i>G</i><sub>0</sub>(<i>x</i>).'),
            ('Expanding in conformal blocks gives the channel data 1, 8/3, 14/3, 58/9, 107/15, … '
             'The 8/3 = 1/2 + 13/6 is the exchange of the two Cartan currents, with the charges 1 '
             'and 13 again. The 14/3 splits as 1 for the stress tensor plus 11/3 for the other '
             'weight-two primaries. The same 11/3 comes out independently from the full table of '
             '113 × 113 × 113 three-point couplings.'),
            ('Data like these go beyond the torus partition function. A lattice model or a '
             'bootstrap study would need them to recognise this particular theory.'),
        ],
        see=[
            'Height: log<sub>10</sub> |<i>G</i><sub>0</sub>(<i>x</i>)|, clipped at 10<sup>3</sup> (the gold caldera floors) and 10<sup>−2.2</sup> (the teal sinkhole floors). The real axis runs left to right; the window −2 ≤ Re <i>x</i> ≤ 3, |Im <i>x</i>| ≤ 2.1 fades out at its edge.',
            'Colour: arg <i>G</i><sub>0</sub>(<i>x</i>), cycling gold, coral, violet, teal. Thin contours every quarter decade, brighter every decade.',
            'Blender Cycles render of a height field with about 840,000 vertices.',
        ],
        work=('Section 3, exact correlators and channel data (p. 13): eq. (28), the fifteen-term '
              'derivation and the global-block coefficients. The independent 11/3 cross-check is '
              'in <span class="mono">c8_physics_20260927/crosslink_checks.json</span>.'),
    ),
    dict(
        slug='cities', img='r7_two_cities', accent='gold',
        kicker='The physics',
        title='Two theories, one central charge',
        dek=('The same chiral algebra builds two different worlds. Only one of them can be pushed '
             'off criticality by a relevant scalar.'),
        alt=('Two night cities of glowing bars side by side. The left city is dense, with gold, '
             'violet and coral bars and seven lit towers near the front corner; the right city has '
             'a sparse grid of gold bars.'),
        body=[
            ('A chiral algebra does not by itself fix a full theory. Left and right movers still '
             'have to be paired. Pair each of <i>U</i>\'s twelve sectors with itself and you get '
             'the diagonal theory on the left. Extend <i>U</i> to <i>E</i><sub>8</sub> on both '
             'sides and you get the <i>E</i><sub>8</sub> theory with Haagerup lines on the right. '
             'Both have <i>c</i> = 8 in each chirality. They have the same free energy, '
             '−4π<i>T</i><sup>2</sup>/3<i>v</i> per unit length, and the same entanglement '
             'coefficient, 8/3.'),
            ('Their spectra are very different. Each bar stands at a pair of conformal weights '
             '(<i>h</i>, <i>h̄</i>), and its height counts the Virasoro primaries there, from the '
             'exact spectrum computed through dimension 24. The diagonal theory crowds bars at '
             'thirds and thirteenths. Below the coral line Δ = 2, seven glowing scalar towers hold '
             '9, 25, 49, 169, 196, 729 and 1,764 relevant scalars, 2,941 in all. The '
             '<i>E</i><sub>8</sub> theory has integer weights only, and no scalar below the line.'),
            ('The difference is physical. Relevant scalars are the knobs that drive a critical '
             'system away from criticality. In the ordinary modular bootstrap of Collier, Lin and '
             'Yin, the <i>E</i><sub>8</sub> theory sits at the kink at (<i>c</i>, Δ) = (8, 2), '
             'while the diagonal theory sits deep inside the allowed region at (8, 2/3).'),
            ('Yet the symmetry sees what they share. Keep only the states that every symmetry line '
             'leaves alone: the twelve Verlinde lines on the left, the Haagerup lines of the first '
             '<i>E</i><sub>8</sub> factor on the right. In both, the first such scalar has '
             'dimension 2, with 36 components on the left and 1,488 on the right.'),
        ],
        see=[
            'Bar at (<i>h</i>, <i>h̄</i>), height log<sub>10</sub>(1 + number of Virasoro primaries). Weights up to 3 on each side, from the exported spectrum tables.',
            'Colour: gold for the integer-weight sectors (0, <i>b</i>, <i>a</i>, <i>c</i><sub>0</sub>), violet for <i>c</i><sub>1</sub> and <i>c</i><sub>2</sub>, coral for <i>d</i><sub>1</sub>, …, <i>d</i><sub>6</sub>. White caps: the relevant scalars.',
            'Floor: the integer grid, the scalar diagonal <i>h</i> = <i>h̄</i> (gold) and the marginal line Δ = <i>h</i> + <i>h̄</i> = 2 (coral). Blender Cycles render.',
        ],
        work=('Section 2, characters and a spin-resolved spectrum (p. 7), and eq. (10), the seven '
              'relevant scalar levels (p. 9). Section 7, coordinates for published exclusion plots '
              '(p. 26).'),
    ),
]
