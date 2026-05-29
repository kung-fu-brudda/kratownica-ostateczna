// 3D Truss Analyzer JS Logic

// Global state variables
let scene, camera, renderer, controls;
let nodeMeshes = [];
let memberMeshes = [];
let supportMeshes = [];
let arrowHelpers = [];
let labelOverlayElements = [];

// Pico Hardware Integration Variables
let isPicoLiveMode = false;
let picoForces = new Array(18).fill(0);
let picoConnectionState = 'disconnected'; // 'disconnected', 'connecting', 'connected'
let serialPort = null;
let serialReader = null;
let webSocket = null;
let httpPollInterval = null;
let picoSimInterval = null;
let picoSimulationActive = false;
let serialBuffer = '';

// Solver & Truss Config
const AE = 1e6; // N, Axial Stiffness (constant for simplicity)

// Members definition
const members = [
    { n1: 0, n2: 1, name: "Pręt 0-1" },
    { n1: 1, n2: 2, name: "Pręt 1-2" },
    { n1: 3, n2: 4, name: "Pręt 3-4" },
    { n1: 7, n2: 6, name: "Pręt 7-6" },
    { n1: 10, n2: 9, name: "Pręt 10-9" },
    { n1: 9, n2: 8, name: "Pręt 9-8" },
    { n1: 1, n2: 3, name: "Pręt 1-3" },
    { n1: 2, n2: 4, name: "Pręt 2-4" },
    { n1: 4, n2: 5, name: "Pręt 4-5" },
    { n1: 5, n2: 6, name: "Pręt 5-6" },
    { n1: 6, n2: 8, name: "Pręt 6-8" },
    { n1: 7, n2: 9, name: "Pręt 7-9" },
    { n1: 0, n2: 3, name: "Pręt 0-3" },
    { n1: 2, n2: 3, name: "Pręt 2-3" },
    { n1: 3, n2: 5, name: "Pręt 3-5" },
    { n1: 5, n2: 7, name: "Pręt 5-7" },
    { n1: 7, n2: 8, name: "Pręt 7-8" },
    { n1: 7, n2: 10, name: "Pręt 7-10" }
];

// Linear System Solver (Gaussian Elimination)
function solveLinearSystem(A, b) {
    const n = b.length;
    // Deep copy matrix A and vector b
    const A_copy = A.map(row => [...row]);
    const b_copy = [...b];
    
    for (let i = 0; i < n; i++) {
        // Pivot selection
        let maxEl = Math.abs(A_copy[i][i]);
        let maxRow = i;
        for (let k = i + 1; k < n; k++) {
            if (Math.abs(A_copy[k][i]) > maxEl) {
                maxEl = Math.abs(A_copy[k][i]);
                maxRow = k;
            }
        }
        
        // Swap rows in A and b
        const tempRow = A_copy[i];
        A_copy[i] = A_copy[maxRow];
        A_copy[maxRow] = tempRow;
        
        const tempB = b_copy[i];
        b_copy[i] = b_copy[maxRow];
        b_copy[maxRow] = tempB;
        
        // Check for singularity
        if (Math.abs(A_copy[i][i]) < 1e-9) {
            A_copy[i][i] = 1e-9; // simple regularization
        }
        
        // Elimination
        for (let k = i + 1; k < n; k++) {
            const c = -A_copy[k][i] / A_copy[i][i];
            for (let j = i; j < n; j++) {
                if (i === j) {
                    A_copy[k][j] = 0;
                } else {
                    A_copy[k][j] += c * A_copy[i][j];
                }
            }
            b_copy[k] += c * b_copy[i];
        }
    }
    
    // Back substitution
    const x = new Array(n).fill(0);
    for (let i = n - 1; i >= 0; i--) {
        x[i] = b_copy[i] / A_copy[i][i];
        for (let k = i - 1; k >= 0; k--) {
            b_copy[k] -= A_copy[k][i] * x[i];
        }
    }
    return x;
}

// Full Truss FEM Solver
function calculateTruss(a, b, P1, P2, P3, alpha, P4, beta) {
    // 1. Define nodes coordinates (in mm)
    const nodes = [
        { x: 0, y: 0 },             // 0: Bottom-left support (pinned)
        { x: 0, y: b },             // 1: Mid-left vertical column
        { x: 0, y: 2 * b },         // 2: Top-left corner
        { x: 0.5 * a, y: b },       // 3: Mid-left inner node
        { x: 0.5 * a, y: 2 * b },   // 4: Top-left inner node
        { x: a, y: 2 * b },         // 5: Top-center node
        { x: 1.5 * a, y: 2 * b },   // 6: Top-right inner node
        { x: 1.5 * a, y: b },       // 7: Mid-right inner node
        { x: 2 * a, y: 2 * b },     // 8: Top-right corner
        { x: 2 * a, y: b },         // 9: Mid-right vertical column
        { x: 2 * a, y: 0 }          // 10: Bottom-right support (roller)
    ];

    const numNodes = nodes.length;
    const numDOFs = 2 * numNodes;

    // 2. Build Force Vector F
    const F = new Array(numDOFs).fill(0);
    
    // P1 acting downwards at node 2 (top-left)
    F[2 * 2 + 1] = -P1;
    
    // P2 acting downwards at node 6 (top-right inner)
    F[2 * 6 + 1] = -P2;
    
    // P3 acting at node 4 (top-left inner), angle alpha with vertical (pointing down-right)
    const alphaRad = (alpha * Math.PI) / 180;
    F[2 * 4 + 0] = P3 * Math.sin(alphaRad);
    F[2 * 4 + 1] = -P3 * Math.cos(alphaRad);
    
    // P4 acting at node 1 (mid-left vertical), angle beta with vertical (pointing down-left)
    const betaRad = (beta * Math.PI) / 180;
    F[2 * 1 + 0] = -P4 * Math.sin(betaRad);
    F[2 * 1 + 1] = -P4 * Math.cos(betaRad);

    // 3. Build Global Stiffness Matrix K
    const K = Array.from({ length: numDOFs }, () => new Array(numDOFs).fill(0));

    members.forEach(m => {
        const n1 = nodes[m.n1];
        const n2 = nodes[m.n2];
        const dx = n2.x - n1.x;
        const dy = n2.y - n1.y;
        const L = Math.sqrt(dx * dx + dy * dy);
        const c = dx / L;
        const s = dy / L;
        
        const k = AE / L;
        const k_xx = k * c * c;
        const k_xy = k * c * s;
        const k_yy = k * s * s;
        
        const i = m.n1;
        const j = m.n2;
        
        // Node i - Node i
        K[2 * i + 0][2 * i + 0] += k_xx;
        K[2 * i + 0][2 * i + 1] += k_xy;
        K[2 * i + 1][2 * i + 0] += k_xy;
        K[2 * i + 1][2 * i + 1] += k_yy;
        
        // Node j - Node j
        K[2 * j + 0][2 * j + 0] += k_xx;
        K[2 * j + 0][2 * j + 1] += k_xy;
        K[2 * j + 1][2 * j + 0] += k_xy;
        K[2 * j + 1][2 * j + 1] += k_yy;
        
        // Node i - Node j
        K[2 * i + 0][2 * j + 0] -= k_xx;
        K[2 * i + 0][2 * j + 1] -= k_xy;
        K[2 * i + 1][2 * j + 0] -= k_xy;
        K[2 * i + 1][2 * j + 1] -= k_yy;
        
        // Node j - Node i
        K[2 * j + 0][2 * i + 0] -= k_xx;
        K[2 * j + 0][2 * i + 1] -= k_xy;
        K[2 * j + 1][2 * i + 0] -= k_xy;
        K[2 * j + 1][2 * i + 1] -= k_yy;
    });

    // 4. Boundary Conditions
    // Pinned support at node 0 (constrained ux, uy)
    // Roller support at node 10 (constrained uy, ux is free)
    const constraints = [2 * 0 + 0, 2 * 0 + 1, 2 * 10 + 1];
    const freeDOFs = [];
    for (let d = 0; d < numDOFs; d++) {
        if (!constraints.includes(d)) {
            freeDOFs.push(d);
        }
    }

    // Partition Stiffness Matrix and Load Vector
    const K_free = freeDOFs.map(r => freeDOFs.map(c => K[r][c]));
    const F_free = freeDOFs.map(r => F[r]);

    // Solve for displacements at free DOFs
    const u_free = solveLinearSystem(K_free, F_free);

    // Reconstruct full displacement vector u
    const u = new Array(numDOFs).fill(0);
    freeDOFs.forEach((dof, idx) => {
        u[dof] = u_free[idx];
    });

    // 5. Calculate Member Forces and stresses
    const memberForces = members.map(m => {
        const n1 = nodes[m.n1];
        const n2 = nodes[m.n2];
        const dx = n2.x - n1.x;
        const dy = n2.y - n1.y;
        const L = Math.sqrt(dx * dx + dy * dy);
        const c = dx / L;
        const s = dy / L;
        
        const u1x = u[2 * m.n1];
        const u1y = u[2 * m.n1 + 1];
        const u2x = u[2 * m.n2];
        const u2y = u[2 * m.n2 + 1];
        
        const dux = u2x - u1x;
        const duy = u2y - u1y;
        
        const force = (AE / L) * (dux * c + duy * s);
        return force;
    });

    // 6. Calculate Support Reactions
    // R_d = sum(K_d,j * u_j) - F_d
    const R_Ax = K[2 * 0 + 0].reduce((sum, val, idx) => sum + val * u[idx], 0) - F[2 * 0 + 0];
    const R_Ay = K[2 * 0 + 1].reduce((sum, val, idx) => sum + val * u[idx], 0) - F[2 * 0 + 1];
    const R_By = K[2 * 10 + 1].reduce((sum, val, idx) => sum + val * u[idx], 0) - F[2 * 10 + 1];

    return {
        nodes,
        displacements: u,
        forces: memberForces,
        reactions: { R_Ax, R_Ay, R_By }
    };
}

// Classify stresses based on percentage of max force
function getStressCategory(force, maxForce) {
    if (maxForce === 0) return 'light-green';
    
    const ratio = Math.abs(force) / maxForce;
    if (ratio < 0.01 || Math.abs(force) < 1.0) {
        return 'light-green'; // Pręty zerowe
    } else if (ratio < 0.30) {
        return 'dark-green';  // Niskie obciążenie
    } else if (ratio < 0.70) {
        return 'blue';        // Pośrednio obciążone
    } else {
        return 'red';         // Najbardziej obciążone
    }
}

// Get color hex for stress category
function getStressColor(category) {
    switch (category) {
        case 'red': return 0xff3366;
        case 'blue': return 0x0077ff;
        case 'dark-green': return 0x00a86b;
        case 'light-green': default: return 0x39ff14;
    }
}

// Initialize Three.js 3D viewport
function init3D() {
    const container = document.getElementById('canvas3d');
    const width = container.clientWidth || 400;
    const height = container.clientHeight || 400;

    // Scene
    scene = new THREE.Scene();
    scene.background = null; // transparent to show gradient background of CSS viewport

    // Camera
    camera = new THREE.PerspectiveCamera(45, width / height, 1, 5000);
    camera.position.set(0, 200, 700);

    // Renderer
    renderer = new THREE.WebGLRenderer({ antialias: true, alpha: true });
    renderer.setSize(width, height);
    renderer.setPixelRatio(window.devicePixelRatio);
    renderer.shadowMap.enabled = true;
    renderer.shadowMap.type = THREE.PCFSoftShadowMap;
    container.appendChild(renderer.domElement);

    // Controls
    controls = new THREE.OrbitControls(camera, renderer.domElement);
    controls.enableDamping = true;
    controls.dampingFactor = 0.05;
    controls.screenSpacePanning = true;
    controls.maxPolarAngle = Math.PI / 2 + 0.1; // Don't go below ground too much
    controls.minDistance = 100;
    controls.maxDistance = 1500;

    // Lights
    const ambientLight = new THREE.AmbientLight(0xffffff, 0.45);
    scene.add(ambientLight);

    const dirLight1 = new THREE.DirectionalLight(0xffffff, 0.8);
    dirLight1.position.set(200, 500, 300);
    dirLight1.castShadow = true;
    dirLight1.shadow.mapSize.width = 1024;
    dirLight1.shadow.mapSize.height = 1024;
    scene.add(dirLight1);

    const dirLight2 = new THREE.DirectionalLight(0xffffff, 0.35);
    dirLight2.position.set(-200, 200, -300);
    scene.add(dirLight2);

    const gridHelper = new THREE.GridHelper(1000, 20, 0x3a4f7c, 0x1f2e4e);
    gridHelper.position.y = -100; // Place grid slightly below supports
    scene.add(gridHelper);

    // Setup window resize listener
    window.addEventListener('resize', onWindowResize);
    
    // Start animation loop
    animate();
}

function onWindowResize() {
    const container = document.getElementById('canvas3d');
    const width = container.clientWidth;
    const height = container.clientHeight;
    
    camera.aspect = width / height;
    camera.updateProjectionMatrix();
    
    renderer.setSize(width, height);
}

function animate() {
    requestAnimationFrame(animate);
    
    controls.update();
    updateFloatingLabels();
    
    renderer.render(scene, camera);
}

// Clear all meshes from the 3D scene
function clearScene() {
    nodeMeshes.forEach(mesh => scene.remove(mesh));
    nodeMeshes = [];
    
    memberMeshes.forEach(mesh => scene.remove(mesh));
    memberMeshes = [];
    
    supportMeshes.forEach(mesh => scene.remove(mesh));
    supportMeshes = [];
    
    arrowHelpers.forEach(arrow => scene.remove(arrow));
    arrowHelpers = [];

    // Clear HTML labels
    labelOverlayElements.forEach(item => {
        if (item.element) {
            item.element.remove();
        }
    });
    labelOverlayElements = [];
}

// Draw or update 3D Scene based on solve results
function updateVisualization(solveResults, showLabels, showForces, deformTruss) {
    clearScene();

    const { nodes, displacements, forces } = solveResults;
    const maxForce = Math.max(...forces.map(Math.abs));

    // Scale displacement for display (deformation amplification)
    const defScale = deformTruss ? 100.0 : 0.0;

    // Center coordinates in 3D: offset by half truss width & height
    const dimA = parseFloat(document.getElementById('dim-a').value);
    const dimB = parseFloat(document.getElementById('dim-b').value);
    const offsetX = dimA;
    const offsetY = dimB;

    // Calculate actual 3D positions of nodes (offsetted to center around 3D origin)
    const nodePositions3D = nodes.map((n, idx) => {
        const ux = displacements[2 * idx] * defScale;
        const uy = displacements[2 * idx + 1] * defScale;
        return new THREE.Vector3(
            (n.x + ux) - offsetX,
            (n.y + uy) - offsetY,
            0 // 2D truss in Z = 0 plane
        );
    });

    // Material templates
    const nodeMaterial = new THREE.MeshStandardMaterial({
        color: 0xcccccc,
        roughness: 0.2,
        metalness: 0.8
    });

    const supportMaterial = new THREE.MeshStandardMaterial({
        color: 0x666666,
        roughness: 0.4,
        metalness: 0.5
    });

    // 1. Draw Nodes
    nodePositions3D.forEach((pos, idx) => {
        const sphereGeo = new THREE.SphereGeometry(12, 32, 32);
        const sphereMesh = new THREE.Mesh(sphereGeo, nodeMaterial);
        sphereMesh.position.copy(pos);
        sphereMesh.castShadow = true;
        sphereMesh.receiveShadow = true;
        scene.add(sphereMesh);
        nodeMeshes.push(sphereMesh);

        // Add 3D text/HTML labels if checkbox is checked
        if (showLabels) {
            createFloatingLabel(`Węzeł ${idx}`, pos, 'node-label');
        }
    });

    // 2. Draw Members (Cylinders connecting nodes)
    members.forEach((m, idx) => {
        const p1 = nodePositions3D[m.n1];
        const p2 = nodePositions3D[m.n2];
        const force = forces[idx];
        const category = getStressCategory(force, maxForce);
        const color = getStressColor(category);

        // Create a cylinder connecting p1 and p2
        const distance = p1.distanceTo(p2);
        const position = p1.clone().add(p2).multiplyScalar(0.5); // Midpoint

        // Cylinder geometry aligned with Y axis by default, we need to rotate it
        const cylinderGeo = new THREE.CylinderGeometry(6, 6, distance, 16);
        
        const memberMat = new THREE.MeshStandardMaterial({
            color: color,
            roughness: 0.3,
            metalness: 0.7,
            emissive: color,
            emissiveIntensity: 0.15
        });
        
        const cylinderMesh = new THREE.Mesh(cylinderGeo, memberMat);
        cylinderMesh.position.copy(position);

        // Orient cylinder from p1 to p2
        const direction = new THREE.Vector3().subVectors(p2, p1).normalize();
        const alignAxis = new THREE.Vector3(0, 1, 0); // Default cylinder direction
        cylinderMesh.quaternion.setFromUnitVectors(alignAxis, direction);
        cylinderMesh.castShadow = true;
        cylinderMesh.receiveShadow = true;

        scene.add(cylinderMesh);
        memberMeshes.push(cylinderMesh);

        // Label for member midpoint
        if (showLabels) {
            createFloatingLabel(m.name, position, 'member-label');
        }
    });

    // 3. Draw Supports (Node 0 - Pinned, Node 10 - Roller)
    // Pinned Support (Cone pointing up + baseplate block)
    const posA = nodePositions3D[0];
    const supportAGroup = new THREE.Group();
    
    const coneGeoA = new THREE.ConeGeometry(18, 25, 4);
    const coneMeshA = new THREE.Mesh(coneGeoA, supportMaterial);
    coneMeshA.position.y = -12.5; // shift down so apex touches node
    coneMeshA.rotation.y = Math.PI / 4;
    supportAGroup.add(coneMeshA);
    
    const plateGeoA = new THREE.BoxGeometry(30, 6, 30);
    const plateMeshA = new THREE.Mesh(plateGeoA, supportMaterial);
    plateMeshA.position.y = -25;
    supportAGroup.add(plateMeshA);
    
    supportAGroup.position.copy(posA);
    scene.add(supportAGroup);
    supportMeshes.push(supportAGroup);
    createFloatingLabel("Podpora A (Stała)", posA.clone().add(new THREE.Vector3(0, -38, 0)), 'support-label');

    // Roller Support (Cone pointing up + 3 wheels + baseplate block)
    const posB = nodePositions3D[10];
    const supportBGroup = new THREE.Group();
    
    const coneMeshB = coneMeshA.clone();
    supportBGroup.add(coneMeshB);
    
    const plateMeshB = plateMeshA.clone();
    supportBGroup.add(plateMeshB);
    
    // Rollers (small cylinders)
    const rollerGeo = new THREE.CylinderGeometry(4, 4, 30, 8);
    rollerGeo.rotateX(Math.PI / 2); // align along Z
    
    const roller1 = new THREE.Mesh(rollerGeo, supportMaterial);
    roller1.position.set(-10, -30, 0);
    supportBGroup.add(roller1);
    
    const roller2 = new THREE.Mesh(rollerGeo, supportMaterial);
    roller2.position.set(10, -30, 0);
    supportBGroup.add(roller2);
    
    supportBGroup.position.copy(posB);
    scene.add(supportBGroup);
    supportMeshes.push(supportBGroup);
    createFloatingLabel("Podpora B (Przesuwna)", posB.clone().add(new THREE.Vector3(0, -42, 0)), 'support-label');

    // 4. Draw Load Vectors (Forces)
    if (showForces && !isPicoLiveMode) {
        const P1_val = parseFloat(document.getElementById('force-p1').value);
        const P2_val = parseFloat(document.getElementById('force-p2').value);
        const P3_val = parseFloat(document.getElementById('force-p3').value);
        const P4_val = parseFloat(document.getElementById('force-p4').value);
        const alpha_val = parseFloat(document.getElementById('angle-alpha').value);
        const beta_val = parseFloat(document.getElementById('angle-beta').value);
        
        // P1 at node 2 (pointing straight down)
        if (P1_val > 0) {
            addForceArrow(nodePositions3D[2], new THREE.Vector3(0, -1, 0), P1_val, `P1: ${P1_val}N`);
        }
        // P2 at node 6 (pointing straight down)
        if (P2_val > 0) {
            addForceArrow(nodePositions3D[6], new THREE.Vector3(0, -1, 0), P2_val, `P2: ${P2_val}N`);
        }
        // P3 at node 4 (inclined down-right by alpha)
        if (P3_val > 0) {
            const aRad = (alpha_val * Math.PI) / 180;
            const dir = new THREE.Vector3(Math.sin(aRad), -Math.cos(aRad), 0).normalize();
            addForceArrow(nodePositions3D[4], dir, P3_val, `P3: ${P3_val}N (&alpha;=${alpha_val}°)`);
        }
        // P4 at node 1 (inclined down-left by beta)
        if (P4_val > 0) {
            const bRad = (beta_val * Math.PI) / 180;
            const dir = new THREE.Vector3(-Math.sin(bRad), -Math.cos(bRad), 0).normalize();
            addForceArrow(nodePositions3D[1], dir, P4_val, `P4: ${P4_val}N (&beta;=${beta_val}°)`);
        }
    }
}

// Add an ArrowHelper representing a load
function addForceArrow(nodePos, direction, forceMagnitude, labelText) {
    const arrowColor = 0xffaa00; // Gold
    
    // Scale arrow length based on force magnitude (max force maps to ~80px/units)
    const baseScale = 80 / 3000; 
    const arrowLength = Math.max(40, forceMagnitude * baseScale);
    
    // Arrow pointing TOWARDS node:
    // Arrow starts at nodePos - direction * length, and points in direction
    const arrowOrigin = nodePos.clone().sub(direction.clone().multiplyScalar(arrowLength + 15)); // add offset for sphere radius
    
    const arrowHelper = new THREE.ArrowHelper(
        direction,
        arrowOrigin,
        arrowLength,
        arrowColor,
        18, // head length
        10  // head width
    );
    scene.add(arrowHelper);
    arrowHelpers.push(arrowHelper);

    // Label for the force arrow
    const labelPos = arrowOrigin.clone().add(direction.clone().multiplyScalar(-15)); // offset slightly backward from arrow start
    createFloatingLabel(labelText, labelPos, 'force-label');
}

// Helper to create HTML floating labels
function createFloatingLabel(text, position3D, className) {
    const el = document.createElement('div');
    el.className = `floating-label ${className}`;
    el.innerHTML = text;
    document.getElementById('canvas3d').appendChild(el);
    
    labelOverlayElements.push({
        element: el,
        pos3D: position3D.clone()
    });
}

// Project 3D labels onto 2D viewport coordinates
function updateFloatingLabels() {
    const container = document.getElementById('canvas3d');
    const width = container.clientWidth;
    const height = container.clientHeight;
    
    const tempV = new THREE.Vector3();
    
    labelOverlayElements.forEach(item => {
        tempV.copy(item.pos3D);
        tempV.project(camera);
        
        // Check if node is behind camera
        if (tempV.z > 1) {
            item.element.style.display = 'none';
            return;
        }
        
        // Map to 2D screen coordinates
        const x = (tempV.x *  .5 + .5) * width;
        const y = (tempV.y * -.5 + .5) * height;
        
        item.element.style.display = 'block';
        item.element.style.left = `${x}px`;
        item.element.style.top = `${y}px`;
    });
}

// Populate the "ODCZYTY TENSOMETRÓW" results table
function updateResultsTable(forces) {
    const tbody = document.getElementById('results-body');
    tbody.innerHTML = '';
    
    const maxForce = Math.max(...forces.map(Math.abs));
    
    members.forEach((m, idx) => {
        const force = forces[idx];
        const category = getStressCategory(force, maxForce);
        
        let typeText = '';
        let typeClass = '';
        if (Math.abs(force) < 1.0) {
            typeText = 'Zerowy';
            typeClass = 'zero-force';
        } else if (force > 0) {
            typeText = 'Rozciąganie';
            typeClass = 'tension';
        } else {
            typeText = 'Ściskanie';
            typeClass = 'compression';
        }
        
        const row = document.createElement('tr');
        row.innerHTML = `
            <td>
                <span class="status-dot ${category}"></span>
                ${m.name}
            </td>
            <td class="num-col ${typeClass}">
                ${force.toFixed(1)}
            </td>
            <td class="${typeClass}">
                ${typeText}
            </td>
        `;
        tbody.appendChild(row);
    });
}

// Support Reactions from live forces calculation helper
function getMemberVector(nodes, m) {
    const n1 = nodes[m.n1];
    const n2 = nodes[m.n2];
    const dx = n2.x - n1.x;
    const dy = n2.y - n1.y;
    const L = Math.sqrt(dx * dx + dy * dy);
    if (L < 1e-9) return { x: 0, y: 0 };
    return { x: dx / L, y: dy / L };
}

function calculateLiveReactions(nodes, forces) {
    // Node 0 connected: members 0 and 12
    const u0 = getMemberVector(nodes, members[0]);
    const u12 = getMemberVector(nodes, members[12]);
    const F0 = forces[0] || 0;
    const F12 = forces[12] || 0;
    
    const R_Ax = - (F0 * u0.x + F12 * u12.x);
    const R_Ay = - (F0 * u0.y + F12 * u12.y);
    
    // Node 10 connected: members 4 and 17
    // Member 4: n1=10, n2=9 (node 10 is n1, force is +F4 * u4)
    // Member 17: n1=7, n2=10 (node 10 is n2, force is -F17 * u17)
    const u4 = getMemberVector(nodes, members[4]);
    const u17 = getMemberVector(nodes, members[17]);
    const F4 = forces[4] || 0;
    const F17 = forces[17] || 0;
    
    const R_By = - (F4 * u4.y - F17 * u17.y);
    
    return { R_Ax, R_Ay, R_By };
}

// Main logic coordinator
function solveAndRedraw() {
    // Read input values
    const a = parseFloat(document.getElementById('dim-a').value);
    const b = parseFloat(document.getElementById('dim-b').value);
    
    const P1 = parseFloat(document.getElementById('force-p1').value);
    const P2 = parseFloat(document.getElementById('force-p2').value);
    const P3 = parseFloat(document.getElementById('force-p3').value);
    const alpha = parseFloat(document.getElementById('angle-alpha').value);
    const P4 = parseFloat(document.getElementById('force-p4').value);
    const beta = parseFloat(document.getElementById('angle-beta').value);
    
    const showLabels = document.getElementById('show-labels').checked;
    const showForces = document.getElementById('show-forces').checked;
    const deformTruss = document.getElementById('deform-truss').checked;

    // Toggle slider disabling based on mode
    const forceIds = ['force-p1', 'force-p2', 'force-p3', 'angle-alpha', 'force-p4', 'angle-beta'];
    forceIds.forEach(id => {
        const el = document.getElementById(id);
        el.disabled = isPicoLiveMode;
        el.closest('.input-group').style.opacity = isPicoLiveMode ? '0.5' : '1';
    });

    let results;
    if (isPicoLiveMode) {
        // Live Pico Mode: compute geometry at zero external load
        const geom = calculateTruss(a, b, 0, 0, 0, 0, 0, 0);
        const liveForces = [...picoForces];
        const reactions = calculateLiveReactions(geom.nodes, liveForces);
        
        // Zero displacements for live rendering since displacement is not measured
        const displacements = new Array(geom.nodes.length * 2).fill(0);
        
        results = {
            nodes: geom.nodes,
            displacements: displacements,
            forces: liveForces,
            reactions: reactions
        };
    } else {
        // Simulation Mode
        results = calculateTruss(a, b, P1, P2, P3, alpha, P4, beta);
    }

    // Update UI elements values
    document.getElementById('val-a').textContent = a;
    document.getElementById('val-b').textContent = b;
    document.getElementById('val-p1').textContent = P1;
    document.getElementById('val-p2').textContent = P2;
    document.getElementById('val-p3').textContent = P3;
    document.getElementById('val-alpha').textContent = alpha;
    document.getElementById('val-p4').textContent = P4;
    document.getElementById('val-beta').textContent = beta;

    // Update Reactions display
    document.getElementById('react-ax').textContent = results.reactions.R_Ax.toFixed(1);
    document.getElementById('react-ay').textContent = results.reactions.R_Ay.toFixed(1);
    document.getElementById('react-by').textContent = results.reactions.R_By.toFixed(1);

    // Update 3D Canvas
    updateVisualization(results, showLabels, showForces, deformTruss);

    // Update Table
    updateResultsTable(results.forces);
}

// Attach event listeners to all control inputs
function bindUIEvents() {
    const inputs = [
        'dim-a', 'dim-b', 
        'force-p1', 'force-p2', 'force-p3', 'angle-alpha', 'force-p4', 'angle-beta',
        'show-labels', 'show-forces', 'deform-truss'
    ];
    
    inputs.forEach(id => {
        const el = document.getElementById(id);
        if (el.type === 'checkbox') {
            el.addEventListener('change', solveAndRedraw);
        } else {
            el.addEventListener('input', solveAndRedraw);
        }
    });
}

// Inject floating label styles inside the document head dynamically
function injectDynamicCSS() {
    const style = document.createElement('style');
    style.innerHTML = `
        .floating-label {
            position: absolute;
            transform: translate(-50%, -50%);
            font-size: 0.65rem;
            color: #ffffff;
            background: rgba(10, 12, 22, 0.85);
            border: 1px solid rgba(255, 255, 255, 0.1);
            padding: 2px 6px;
            border-radius: 4px;
            pointer-events: none;
            user-select: none;
            z-index: 5;
            white-space: nowrap;
            box-shadow: 0 2px 4px rgba(0, 0, 0, 0.5);
            font-family: 'Inter', sans-serif;
            transition: opacity 0.15s ease;
        }
        .node-label {
            font-size: 0.6rem;
            color: var(--accent);
            background: rgba(0, 0, 0, 0.8);
            border-color: rgba(0, 229, 255, 0.2);
            font-weight: 600;
        }
        .member-label {
            color: #ccc;
            font-size: 0.58rem;
            background: rgba(18, 22, 35, 0.9);
            border: none;
        }
        .force-label {
            color: #ffd700;
            border-color: rgba(255, 215, 0, 0.3);
            font-weight: 500;
            font-size: 0.65rem;
        }
        .support-label {
            font-size: 0.6rem;
            color: #aaa;
            background: rgba(30, 30, 30, 0.8);
            border: none;
        }
        
        @media (max-width: 767px) {
            .floating-label {
                font-size: 0.65rem !important;
                padding: 2px 4px !important;
            }
            .node-label {
                font-size: 0.6rem !important;
            }
            .member-label {
                font-size: 0.58rem !important;
            }
            .force-label {
                font-size: 0.65rem !important;
            }
            .support-label {
                font-size: 0.6rem !important;
            }
        }
    `;
    document.head.appendChild(style);
}

// Pico Connection Status Visualizer
function updatePicoUIStatus(state, message) {
    picoConnectionState = state;
    const statusText = document.getElementById('pico-status');
    const glowDot = document.getElementById('pico-glow-dot');
    
    statusText.textContent = message || (state === 'connected' ? 'Połączono' : state === 'connecting' ? 'Łączenie...' : 'Rozłączono');
    
    statusText.className = '';
    glowDot.className = 'status-glow-dot';
    
    if (state === 'connected') {
        statusText.classList.add('status-connected');
        glowDot.classList.add('connected');
        document.getElementById('btn-usb-connect').disabled = true;
        document.getElementById('btn-usb-disconnect').disabled = false;
        document.getElementById('btn-wifi-connect').disabled = true;
        document.getElementById('btn-wifi-disconnect').disabled = false;
    } else if (state === 'connecting') {
        statusText.classList.add('status-connecting');
        glowDot.classList.add('connecting');
        document.getElementById('btn-usb-connect').disabled = true;
        document.getElementById('btn-usb-disconnect').disabled = true;
        document.getElementById('btn-wifi-connect').disabled = true;
        document.getElementById('btn-wifi-disconnect').disabled = true;
    } else {
        statusText.classList.add('status-disconnected');
        glowDot.classList.add('disconnected');
        document.getElementById('btn-usb-connect').disabled = false;
        document.getElementById('btn-usb-disconnect').disabled = true;
        document.getElementById('btn-wifi-connect').disabled = false;
        document.getElementById('btn-wifi-disconnect').disabled = true;
    }
}

// Log message to Raw Data Log screen
function logPicoData(text) {
    const logEl = document.getElementById('pico-log');
    if (!logEl) return;
    const timeStr = new Date().toLocaleTimeString();
    logEl.textContent = `[${timeStr}] ${text}\n` + logEl.textContent.split('\n').slice(0, 10).join('\n');
}

// Parse Pico message: comma-separated or JSON
function parsePicoMessage(text) {
    text = text.trim();
    if (!text) return;
    
    try {
        let forces = [];
        if (text.startsWith('{')) {
            const data = JSON.parse(text);
            if (data && Array.isArray(data.forces)) {
                forces = data.forces.map(Number);
            } else if (data && Array.isArray(data.data)) {
                forces = data.data.map(Number);
            }
        } else {
            forces = text.split(',').map(Number);
        }
        
        if (forces.length === 18 && forces.every(n => !isNaN(n))) {
            picoForces = forces;
            logPicoData(`Siły: ${forces.map(f => f.toFixed(1)).join(', ')}`);
            if (isPicoLiveMode) {
                solveAndRedraw();
            }
        } else {
            logPicoData(`Błąd formatu: Odebrano ${forces.length}/18 wartości: "${text.substring(0, 45)}"`);
        }
    } catch (e) {
        logPicoData(`Błąd parsowania: "${text.substring(0, 45)}" (${e.message})`);
    }
}

// Web Serial Reader loop
async function startSerialRead() {
    const textDecoder = new TextDecoderStream();
    const readableStreamClosed = serialPort.readable.pipeTo(textDecoder.writable);
    const reader = textDecoder.readable.getReader();
    serialReader = reader;
    
    try {
        while (true) {
            const { value, done } = await reader.read();
            if (done) break;
            if (value) {
                serialBuffer += value;
                let lines = serialBuffer.split('\n');
                serialBuffer = lines.pop(); // keep last incomplete chunk
                for (const line of lines) {
                    if (line.trim()) {
                        parsePicoMessage(line);
                    }
                }
            }
        }
    } catch (error) {
        if (serialPort) {
            logPicoData(`Błąd odczytu: ${error.message}`);
        }
    } finally {
        try {
            reader.releaseLock();
        } catch (e) {}
    }
}

// Connect/Disconnect Serial (USB)
async function connectSerial() {
    if (!navigator.serial) {
        alert("Web Serial API nie jest obsługiwane w tej przeglądarce. Użyj Chrome lub Edge.");
        logPicoData("Web Serial API nieobsługiwane.");
        return;
    }
    
    updatePicoUIStatus('connecting', 'Łączenie...');
    const baudRate = parseInt(document.getElementById('pico-baud').value) || 115200;
    
    try {
        serialPort = await navigator.serial.requestPort();
        await serialPort.open({ baudRate });
        updatePicoUIStatus('connected', 'USB (Połączono)');
        logPicoData(`Połączono szeregowo USB @ ${baudRate} baud`);
        
        // Start async read loop
        startSerialRead();
    } catch (e) {
        updatePicoUIStatus('disconnected', 'Rozłączono');
        logPicoData(`Błąd USB: ${e.message}`);
        console.error(e);
    }
}

async function disconnectSerial() {
    logPicoData("Rozłączanie USB...");
    if (serialReader) {
        try {
            await serialReader.cancel();
        } catch (e) {}
        serialReader = null;
    }
    if (serialPort) {
        try {
            await serialPort.close();
        } catch (e) {}
        serialPort = null;
    }
    updatePicoUIStatus('disconnected', 'Rozłączono');
    logPicoData("Rozłączono USB.");
}

// WebSocket Connection (Wi-Fi)
function connectWiFiWS(ip) {
    updatePicoUIStatus('connecting', 'Łączenie...');
    logPicoData(`Łączenie WS ws://${ip}...`);
    
    try {
        let wsUrl = ip;
        if (!wsUrl.startsWith('ws://') && !wsUrl.startsWith('wss://')) {
            wsUrl = `ws://${ip}`;
        }
        
        webSocket = new WebSocket(wsUrl);
        
        webSocket.onopen = () => {
            updatePicoUIStatus('connected', 'Wi-Fi WS (Połączono)');
            logPicoData(`WebSocket połączony: ${wsUrl}`);
        };
        
        webSocket.onmessage = (event) => {
            parsePicoMessage(event.data);
        };
        
        webSocket.onerror = (error) => {
            logPicoData(`Błąd WebSocket. Sprawdź IP.`);
        };
        
        webSocket.onclose = (event) => {
            updatePicoUIStatus('disconnected', 'Rozłączono');
            logPicoData(`WebSocket zamknięty (kod: ${event.code})`);
            webSocket = null;
        };
    } catch (e) {
        updatePicoUIStatus('disconnected', 'Rozłączono');
        logPicoData(`Błąd WS: ${e.message}`);
    }
}

function disconnectWiFiWS() {
    if (webSocket) {
        webSocket.close();
        webSocket = null;
    }
    updatePicoUIStatus('disconnected', 'Rozłączono');
}

// HTTP Polling (Wi-Fi)
function connectWiFiHTTP(ip) {
    updatePicoUIStatus('connecting', 'Łączenie...');
    logPicoData(`Próba HTTP GET http://${ip}...`);
    
    let url = ip;
    if (!url.startsWith('http://') && !url.startsWith('https://')) {
        url = `http://${ip}`;
    }
    
    fetch(url)
        .then(response => {
            if (!response.ok) throw new Error(`HTTP status ${response.status}`);
            return response.text();
        })
        .then(text => {
            updatePicoUIStatus('connected', 'Wi-Fi HTTP (Połączono)');
            logPicoData(`HTTP Polling aktywny: ${url}`);
            parsePicoMessage(text);
            
            httpPollInterval = setInterval(() => {
                fetch(url)
                    .then(r => {
                        if (!r.ok) throw new Error(`HTTP status ${r.status}`);
                        return r.text();
                    })
                    .then(txt => parsePicoMessage(txt))
                    .catch(err => {
                        logPicoData(`Błąd odpytywania HTTP: ${err.message}`);
                        disconnectWiFiHTTP();
                    });
            }, 1000);
        })
        .catch(e => {
            updatePicoUIStatus('disconnected', 'Rozłączono');
            logPicoData(`Błąd HTTP: ${e.message}`);
        });
}

function disconnectWiFiHTTP() {
    if (httpPollInterval) {
        clearInterval(httpPollInterval);
        httpPollInterval = null;
    }
    updatePicoUIStatus('disconnected', 'Rozłączono');
    logPicoData("Zatrzymano HTTP Polling.");
}

// Developer Simulation Stream generator
function togglePicoSimulation() {
    if (picoSimulationActive) {
        stopPicoSimulation();
    } else {
        startPicoSimulation();
    }
}

function startPicoSimulation() {
    picoSimulationActive = true;
    const testBtn = document.getElementById('btn-pico-test');
    testBtn.textContent = "Zatrzymaj Symulację";
    testBtn.style.backgroundColor = "rgba(255, 51, 102, 0.15)";
    testBtn.style.color = "#ff3366";
    testBtn.style.borderColor = "rgba(255, 51, 102, 0.4)";
    
    updatePicoUIStatus('connected', 'Symulacja (Połączono)');
    logPicoData("Uruchomiono symulator Pico.");
    
    let step = 0;
    picoSimInterval = setInterval(() => {
        const a = parseFloat(document.getElementById('dim-a').value);
        const b = parseFloat(document.getElementById('dim-b').value);
        const P1 = parseFloat(document.getElementById('force-p1').value);
        const P2 = parseFloat(document.getElementById('force-p2').value);
        const P3 = parseFloat(document.getElementById('force-p3').value);
        const alpha = parseFloat(document.getElementById('angle-alpha').value);
        const P4 = parseFloat(document.getElementById('force-p4').value);
        const beta = parseFloat(document.getElementById('angle-beta').value);
        
        // Solve structural math to get base forces
        const theoretical = calculateTruss(a, b, P1, P2, P3, alpha, P4, beta);
        
        // Add dynamic fluctuations (vibrations / sensor noise)
        const noisyForces = theoretical.forces.map((f, idx) => {
            const noise = 15.0 * Math.sin(step * 0.25 + idx) + (Math.random() - 0.5) * 6.0;
            if (Math.abs(f) < 1.0) return noise * 0.1; // Zero forces stay near zero
            return f + noise;
        });
        
        step++;
        
        // Format to CSV string and parse
        const csv = noisyForces.map(n => n.toFixed(2)).join(',');
        parsePicoMessage(csv);
    }, 500);
}

function stopPicoSimulation() {
    picoSimulationActive = false;
    const testBtn = document.getElementById('btn-pico-test');
    testBtn.textContent = "Symuluj Pico";
    testBtn.style.backgroundColor = "rgba(255, 170, 0, 0.1)";
    testBtn.style.color = "#ffaa00";
    testBtn.style.borderColor = "rgba(255, 170, 0, 0.25)";
    
    if (picoSimInterval) {
        clearInterval(picoSimInterval);
        picoSimInterval = null;
    }
    updatePicoUIStatus('disconnected', 'Rozłączono');
    logPicoData("Zatrzymano symulator Pico.");
}

// Bind event listeners for hardware connection card
function setupPicoControls() {
    document.getElementById('pico-mode').addEventListener('change', (e) => {
        isPicoLiveMode = e.target.checked;
        solveAndRedraw();
    });
    
    const tabUsb = document.getElementById('tab-usb');
    const tabWifi = document.getElementById('tab-wifi');
    const panelUsb = document.getElementById('panel-usb');
    const panelWifi = document.getElementById('panel-wifi');
    
    tabUsb.addEventListener('click', () => {
        tabUsb.classList.add('active');
        tabWifi.classList.remove('active');
        panelUsb.classList.add('active');
        panelWifi.classList.remove('active');
    });
    
    tabWifi.addEventListener('click', () => {
        tabWifi.classList.add('active');
        tabUsb.classList.remove('active');
        panelWifi.classList.add('active');
        panelUsb.classList.remove('active');
    });
    
    document.getElementById('btn-usb-connect').addEventListener('click', connectSerial);
    document.getElementById('btn-usb-disconnect').addEventListener('click', disconnectSerial);
    
    document.getElementById('btn-wifi-connect').addEventListener('click', () => {
        const ip = document.getElementById('pico-ip').value.trim();
        const proto = document.getElementById('pico-wifi-proto').value;
        if (!ip) {
            alert("Podaj adres IP lub URL urządzenia Pico.");
            return;
        }
        if (proto === 'ws') {
            connectWiFiWS(ip);
        } else {
            connectWiFiHTTP(ip);
        }
    });
    
    document.getElementById('btn-wifi-disconnect').addEventListener('click', () => {
        if (webSocket) {
            disconnectWiFiWS();
        } else if (httpPollInterval) {
            disconnectWiFiHTTP();
        }
    });
    
    document.getElementById('btn-pico-test').addEventListener('click', togglePicoSimulation);
}

// App Entry Point
document.addEventListener('DOMContentLoaded', () => {
    injectDynamicCSS();
    init3D();
    bindUIEvents();
    setupPicoControls();
    setupMobileNavigation();
    
    // Initial run
    solveAndRedraw();
    
    // Zoom in a bit and center (adjust camera distance for mobile to make the truss fit)
    const isMobile = window.innerWidth < 768;
    camera.position.set(0, 100, isMobile ? 1000 : 550);
    controls.target.set(0, 100, 0);
    controls.update();
});

// Setup mobile bottom tab navigation switching
function setupMobileNavigation() {
    const navButtons = document.querySelectorAll('.mobile-nav-btn');
    const panels = {
        'panel-controls': document.getElementById('panel-controls'),
        'panel-viewport': document.getElementById('panel-viewport'),
        'panel-results': document.getElementById('panel-results')
    };

    navButtons.forEach(btn => {
        btn.addEventListener('click', () => {
            const targetId = btn.getAttribute('data-target');
            
            // Remove active classes
            navButtons.forEach(b => b.classList.remove('active'));
            Object.values(panels).forEach(p => p.classList.remove('active-mobile'));
            
            // Add active classes to selected
            btn.classList.add('active');
            if (panels[targetId]) {
                panels[targetId].classList.add('active-mobile');
            }
            
            // Trigger 3D renderer resize when switching to viewport to avoid stretching
            if (targetId === 'panel-viewport' && typeof onWindowResize === 'function') {
                setTimeout(onWindowResize, 50); // slight delay to allow container layout to calculate sizes
            }
        });
    });
}
