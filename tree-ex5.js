function not_literal(literal) {
    var output
    if (literal.startsWith('!')) {
        return literal.slice(1,2)
    } else {
        return '!' + literal
    } 
}

function contra_positive(implication) {
    return [not_literal(implication[1]), not_literal(implication[0])]
}


// Truth table generation
function countLiterals(imp_set) {
    var uniqueLiterals = []
    for (let i = 0; i < imp_set.length; i++) {
        var imp = imp_set[i]
        if (imp[0].startsWith('!')) {
            var pred = not_literal(imp[0])
        } else {
            var pred = imp[0]
        }
        if (imp[1].startsWith('!')) {
            var cons = not_literal(imp[1])
        } else {
            var cons = imp[1]
        }
        if (!uniqueLiterals.includes(pred)) {
            uniqueLiterals.push(pred)
        }
        if (!uniqueLiterals.includes(cons)) {
            uniqueLiterals.push(cons)
        }
    }
    return uniqueLiterals
}
  
function produce_truth_table(literals_list) {
    var length_down = 2 ** literals_list.length + 1
    var length_across = literals_list.length
    var top_labels = literals_list

    var truth_table = new Array(length_down)
    for (var i = 0; i < length_down; i++) {
        truth_table[i] = new Array(length_across)
    }
    truth_table[0] = top_labels

    for (var lit_num = 0; lit_num < length_across; lit_num++) {
        var num = 1
        var counter = 0
        var change_over = (2 ** (lit_num + 1)) - 1
        for (var i = 0; i < change_over + 1; i++) {
            var range = 2 ** (length_across - lit_num - 1)
            for (var n = 0; n < range; n++) {
                truth_table[n + i*(2 ** (length_across - lit_num - 1)) + 1][lit_num] = num
            }
            counter += 1
            if (num === 1) {
                num = 0
            } else {
                num = 1
            }
        }
    }
    return truth_table
}


function alter_table(truth_table, implication_list) {
    var temp_conjuntions = new Array(truth_table.length - 1)
    for (var i = 0; i < truth_table.length - 1; i++) {
        temp_conjuntions[i] = []
    }

    for (var i = 0; i < implication_list.length; i++) {
        var imp = implication_list[i]
        var pred_negated = false
        var cons_negated = false
        var pred
        var cons
        if (imp[0].startsWith('!')) {
            pred_negated = true
            pred = truth_table[0].indexOf(not_literal(imp[0]))
        } else {
            pred = truth_table[0].indexOf(imp[0])
        }
        if (imp[1].startsWith('!')) {
            cons_negated = true
            cons = truth_table[0].indexOf(not_literal(imp[1]))
        } else {
            cons = truth_table[0].indexOf(imp[1])
        }


        for (var n = 0; n < truth_table.length - 1; n++) {
            var row = truth_table[n + 1]
            if (pred_negated && cons_negated) {
                if (row[pred] === 1) {
                    temp_conjuntions[n].push('T')
                } else if (row[cons] === 1) {
                    temp_conjuntions[n].push('F')
                } else {
                    temp_conjuntions[n].push('T')
                }
            } else if (pred_negated) {
                if (row[pred] === 1) {
                    temp_conjuntions[n].push('T')
                } else if (row[cons] === 0) {
                    temp_conjuntions[n].push('F')
                } else {
                    temp_conjuntions[n].push('T')
                }
            } else if (cons_negated) {
                if (row[pred] === 0) {
                    temp_conjuntions[n].push('T')
                } else if (row[cons] === 1) {
                    temp_conjuntions[n].push('F')
                } else {
                    temp_conjuntions[n].push('T')
                }
            } else {
                if (row[pred] === 0) {
                    temp_conjuntions[n].push('T')
                } else if (row[cons] === 0) {
                    temp_conjuntions[n].push('F')
                } else {
                    temp_conjuntions[n].push('T')
                }
            }
        }
    }

    var output = []
    for (var i = 0; i < temp_conjuntions.length; i++) {
        var row = temp_conjuntions[i]
        var out = 'T'
        for (var n = 0; n < row.length; n++) {
            if (!(out === 'T' && row[n] === 'T')) {
                out = 'F'
            }
        }
        output.push(out)
    }

    for (var i = 0; i < truth_table.length - 1; i++) {
        truth_table[i + 1].push(output[i])
    }
    return truth_table
}




  

// Create Virtual Tree
function create_nodes(implication_list) {
    // Create a resulting object which will be used as a dictionary of the tree nodes
    // Nodes consist of three parts: 
    // Nood->The node itself, Parents->References to parent nodes, Children->References to child nodes
    var nodes = {}

    // Initialize variables for implication, antecedent and consequent
    var imp, antecedent, consequent
    
    // Iterate over all of the available implications
    for (var i = 0; i < implication_list.length; i++) {

        // Section for Regular Implications
        imp = implication_list[i]
        antecedent = imp[0]
        consequent = imp[1]

        // We must check if the antecedent is already in our dictionary, if it is not, then we must add it
        // with the nood being equal to itself and it's list of children consisting of only it's consequent
        if (!(Object.keys(nodes).includes(antecedent))) {
            nodes[antecedent] = {
                nood: antecedent,
                children: [consequent],
                parents: []
            }
        } 
        // But if the node already exists, then we simply add the consequent onto the list of child nodes
        // we only add the consequent if the children list does not already include it
        else {
            if (!nodes[antecedent].children.includes(consequent)) {
                nodes[antecedent].children.push(consequent)
            }
        }

        // We do a similar check to the one above but with the consequent, we first check if the node exists
        // and if it does we add on the antecedent as a parent node
        if (!(Object.keys(nodes).includes(consequent))) {
            nodes[consequent] = {
                nood: consequent,
                children: [],
                parents: [antecedent]
            }
        } else {
            if (!nodes[consequent].parents.includes(antecedent)) {
                nodes[consequent].parents.push(antecedent)
            }
        }

        // Section for Contra-Positive Implication
        // This section mirrors the one above except the implication is first transformed into its contrapositive
        var contra = contra_positive(imp)
        antecedent = contra[0]
        consequent = contra[1]
        if (!(Object.keys(nodes).includes(antecedent))) {
            nodes[antecedent] = {
                nood: antecedent,
                children: [consequent],
                parents: []
            }
        } else {
            if (!nodes[antecedent].children.includes(consequent)) {
                nodes[antecedent].children.push(consequent)
            }
        }

        if (!(Object.keys(nodes).includes(consequent))) {
            nodes[consequent] = {
                nood: consequent,
                children: [],
                parents: [antecedent]
            }
        } else {
            if (!nodes[consequent].parents.includes(antecedent)) {
                nodes[consequent].parents.push(antecedent)
            }
        }
    }
    // We return the dictionary containing all of the possible nodes that reference each other
    return nodes
}

// Function...
function new_join_nodes(nodes_object) {
    // Declare simple variables
    var output = []
    var keys = Object.keys(nodes_object)

    while (keys.length !== 0) {
        var current_key = keys.pop()
        var nodes_to_check = []
        var nodes_added = [current_key]
        var temp_tree = []
        var temp_node = nodes_object[current_key]
        temp_tree.push(temp_node)
        
        for (var i = 0; i < temp_node.children.length; i++) {
            nodes_to_check.push(temp_node.children[i])
        }
        for (var i = 0; i < temp_node.parents.length; i++) {
            nodes_to_check.push(temp_node.parents[i])
        }
        
        while (nodes_to_check.length !== 0) {
            var temp_index = nodes_to_check.pop()
            nodes_added.push(temp_index)
            temp_node = nodes_object[temp_index]
            for (var i = 0; i < temp_node.children.length; i++) {
                if (!(nodes_added.includes(temp_node.children[i]))) {
                    if (!(nodes_to_check.includes(temp_node.children[i]))) {
                        nodes_to_check.push(temp_node.children[i])
                    }
                }
            }
            for (var i = 0; i < temp_node.parents.length; i++) {
                if (!(nodes_added.includes(temp_node.parents[i]))) {
                    if (!(nodes_to_check.includes(temp_node.parents[i]))) {
                        nodes_to_check.push(temp_node.parents[i])
                    }    
                }
            }
            temp_tree.push(temp_node)
            temp_index = keys.indexOf(temp_index)
            if (temp_index > -1) {
                keys.splice(temp_index, 1)
            }
        }
       
        output.push(temp_tree)
    }
    return output
}

function combine_tree_pairs(tree_list) {
    var temp_tree = tree_list.pop()
    var nodes_in_each = [[]]
    for (var i = 0; i < temp_tree.length; i++) {
        nodes_in_each[0].push(temp_tree[i].nood)
    }
    var output = [[temp_tree]]

    for (var i = 0; i < tree_list.length; i++) {
        var to_add = true
        temp_tree = tree_list[i]
        var temp_tree_copy = temp_tree.slice()
        var temp_node = temp_tree_copy.pop()
        var literal = not_literal(temp_node.nood)
        for (var n = 0; n < nodes_in_each.length; n++) {
            if (nodes_in_each[n].includes(literal)) {
                output[n].push(temp_tree)
                to_add = false
                for (var j = 0; j < temp_tree.length; j++) {
                    nodes_in_each[n].push(temp_tree[j].nood)
                }
                break
            } else if (nodes_in_each[n].includes(not_literal(literal))) {
                to_add = false
                break
            }
        }
        if (to_add) {
            output.push([temp_tree])
            temp_list = []
            for (var n = 0; n < temp_tree.length; n++) {
                temp_list.push(temp_tree[n].nood)
            }
            nodes_in_each.push(temp_list)
        }
    }
    return output
}

function produce_valid_trees(tree_list) {
    var output = []
    var imp_list = get_literals()
    for (var i = 0; i < tree_list.length; i++) {
        for (var n = 0; n < tree_list[i].length; n++) {
            outer:
            for (var j = 0; j < tree_list[i][n].length; j++) {
                for (var k = 0; k < imp_list.length; k++) {
                    if (imp_list[k].includes(tree_list[i][n][j].nood)) {
                        output.push(tree_list[i][n])
                        break outer
                    }
                }
            }
        }
    }
    return output
}



function create_links(tree) {
    var output = []
    for (var j = 0; j < tree.length; j++) {
        for (var i = 0; i < tree[j].length; i++) {
            if (tree[j][i].children.length === 0) {
                output.push({
                    source: tree[j][i].nood,
                    target: 'T'
                })
            } else {
                for (var n = 0; n < tree[j][i].children.length; n++) {
                    output.push({
                        source: tree[j][i].nood,
                        target: tree[j][i].children[n]
                    })
                }
            }
            if (tree[j][i].parents.length === 0) {
                output.push({
                    source: 'F',
                    target: tree[j][i].nood
                })
            }
        }
    }
    
    return output
}


function produceUserTree(imp_list, lit_list) {
    var tree = {}
    for (var i = 0; i < lit_list.length; i++) {
        tree[lit_list[i]] = {
            nood: lit_list[i],
            children: [],
            parents: []
        }
    }

    for (var i = 0; i < imp_list.length; i++) {
        var antecedent = imp_list[i][0]
        var consequent = imp_list[i][1]
        tree[antecedent].children.push(consequent)
        tree[consequent].parents.push(antecedent)
    }

    var output = []
    var keys = Object.keys(tree)
    for (var i = 0; i < keys.length; i++) {
        output.push(tree[keys[i]])
    }

    return output
    
}


// SIMPLE FUNCTION TO REMOVE PREVIOUS TREE
function removePrevTree() {
    var container = document.getElementById("graph")
    while (container.firstChild) {
        container.removeChild(container.firstChild)
    }
}



// MAIN FUNCTION TO GENERATE TREE
function generateTree(tree_pairs) {
    // Remove the previous simulation
    removePrevTree()

    var color = d3.scaleOrdinal(d3.schemeCategory20);

    var validStates = document.getElementById('valid-states')
    while (validStates.firstChild) {
        validStates.removeChild(validStates.firstChild)
    }

    var userInput = document.getElementById('userInputTable')
    while (userInput.firstChild) {
        userInput.removeChild(userInput.firstChild)
    }

    document.getElementById('total-evaluations').textContent = ''

    var width = window.innerWidth/12 * 9.5,
        height = 550

    // // Get the data for the tree
    var circles_list = []
    for (var i = 0; i < tree_pairs.length; i++) {
        for (var n = 0; n < tree_pairs[i].length; n++) {
            tree_pairs[i][n].width = width * ((i + 1) / (tree_pairs.length + 1))
            tree_pairs[i][n].height = height * ((n + 1) / (tree_pairs[i].length + 1)) - 20
            circles_list.push(tree_pairs[i][n])
        }
    }
    // Create links from this data
    var links = create_links(tree_pairs)

    // Create circles for each of these nodes
    var nodes = d3.range(circles_list.length).map(function(i) {
        return {
            id: circles_list[i].nood,
            x: circles_list[i].width + (Math.floor(Math.random() * 10)),
            y: circles_list[i].height,
            r: 15,
            category: 0
        };
    });

    nodes.push({
        id:'T',
        x: 2 * width / 5,
        y: 20,
        r: 20,
        category: 1
    })

    nodes.push({
        id:'F',
        x: 2 * width / 5,
        y: height - 25,
        r: 20,
        category: 2
    })


    // Append the svg element
    var colors = d3.scaleOrdinal(d3.schemeCategory20);
    var yCenters = [550/2, 550/9*2, 550/9*7]

    var svg = d3.select("#graph").append("svg")
    // .attr("preserveAspectRatio", "xMinYMin meet")
    .attr("width", width)
    .attr("height", height)
    .on('click', makeLine)
    // Zoom Functionality
    // .call(d3.zoom().on("zoom", function () {
    //     svg.attr("transform", d3.event.transform)
    // })).append('g')

    var canMakeLine = true
    var configurations = []

    function makeLine() {

        if (canMakeLine) {
            var m = d3.mouse(this); 
            line = svg
                .append("line")
                .attr("x1", m[0])
                .attr("y1", m[1])
                .attr("x2", m[0])
                .attr("y2", m[1])
                .attr('class', 'lineCut')
        
            svg.on("mousemove", mousemove);
            svg.on('click', makeLine)
            document.body.onkeyup = function(e) {
                if (e.keyCode == 32) {
                    svg.on('mousemove', null)
                    evaluateLine()
                } 
            }
        }         
            
    }

    function mousemove() {
        var m = d3.mouse(this);
        line.attr("x2", m[0])
            .attr("y2", m[1]);
    }

    // Evaluating user cuts
    function evaluateLine() {
        var lines = d3.selectAll('.lineCut')._groups['0']
        var groups = d3.selectAll('.node')._groups['0']
        var litNodes = []
        var validCheck = true
        
        for (var i = 0; i < groups.length; i++) {
            if (!(groups[i].id == 'T' || groups[i].id == 'F')) {
                litNodes.push(groups[i])
            }
        }

        var nodeChecked = []
        var configuration = {}
        var over_lit = false
        var nodes_crossed = new Set()
        for (var i = 0; i < lines.length; i++) {
            // Check double back
            if (lines[i].x2.baseVal.value > x2 && x2 < x1) {
                if (over_lit) {
                    for (var n = i; n < lines.length - i + 1; n++) {
                        d3.select(lines[n]).remove()
                    }
                    break
                }
                else if (nodes_crossed.size == 0) {
                    d3.select(lines[i]).remove()
                }
            } else if (lines[i].x2.baseVal.value < x2 && x2 > x1) {
                if (over_lit) {
                    for (var n = i; n < lines.length - i + 1; n++) {
                        d3.select(lines[n]).remove()
                    }
                    break
                }
                else if (nodes_crossed.size == 0) {
                    d3.select(lines[i]).remove()
                }
            } else if (nodes_crossed.size == litNodes.length) {
                for (var n = i; n < lines.length - i + 1; n++) {
                    d3.select(lines[n]).remove()
                }
                break
            }
            else {
                var x1 = lines[i].x1.baseVal.value
                var y1 = lines[i].y1.baseVal.value
                var x2 = lines[i].x2.baseVal.value
                var y2 = lines[i].y2.baseVal.value
                
                var gradient = (y2 - y1) / (x2 - x1)
                var c = y1 - gradient * x1
                
                for (var n = 0; n < litNodes.length; n++) {
                    var nodeX = litNodes[n].__data__.x
                    var nodeY = litNodes[n].__data__.y
                    var nodeId = litNodes[n].id
    
                    if (nodeX <= x2) {
                        if (nodeX >= x1) {
                            nodes_crossed.add(litNodes[n])
                            if (!nodeChecked.includes(nodeId)) {
                                nodeChecked.push(nodeId)
                            }
                            var posY = gradient * nodeX + c
                            if (nodeY >= posY) {
                                configuration[nodeId] = -1
                            } else {
                                configuration[nodeId] = 1
                            }
                        } 
                    } else if (nodeX <= x1) {
                        nodes_crossed.add(litNodes[n])
                        if (!nodeChecked.includes(nodeId)) {
                            nodeChecked.push(nodeId)
                        }
                        var posY = gradient * nodeX + c
                        if (nodeY >= posY) {
                            configuration[nodeId] = -1
                        } else {
                            configuration[nodeId] = 1
                        }
                    }
                    
                }
                if (nodes_crossed.size == litNodes.length) {
                    over_lit = true
                }
                if (nodes_crossed.size == 0) {
                    d3.select(lines[i]).remove()
                }
                
            }
        }

        var wrong = []
        if (validCheck) {
            if (evaluateConfig(configuration, litNodes, wrong)) {
                var configurationExist = false
                for (var j = 0; j < configurations.length; j++) {
                    if (isEqual(configurations[j], configuration)) {
                        configurationExist = true
                        break
                    }
                }
                
                if (configurationExist) {
                    console.log('Configuration already exists')
                    for (var i = 0; i < lines.length; i++) {
                        d3.select(lines[i]).remove()
                    }
                    changeFeedback('Configuration already exists.')
                } else {
                    for (var i = 0; i < lines.length; i++) {
                        d3.select(lines[i]).attr('class', 'lineGreyed').attr('stroke', function() { return color(configurations.length)})
                    }
                    configurations.push(configuration)
                    checkAnswer()
                }
                
            } else if (nodes_crossed.size !== litNodes.length) {
                var nodes_missed = []
                for (var k = 0; k < litNodes.length; k++) {
                    if (!nodes_crossed.has(litNodes[k])) {
                        nodes_missed.push(litNodes[k].id)
                    }
                }
                changeFeedback(`You must draw the line above or below every node, you are missing nodes: [${nodes_missed}].`)
                for (var i = 0; i < lines.length; i++) {
                    d3.select(lines[i]).remove()
                }
            }
             else {
                changeFeedback(`There are conflicting literals, you have the literals [${wrong}] with their negations on the same side of the line.`)
                for (var i = 0; i < lines.length; i++) {
                    d3.select(lines[i]).remove()
                }
            }
        } else {
            console.log('Double Back')
            for (var i = 0; i < lines.length; i++) {
                d3.select(lines[i]).remove()
            }
        }

    }

    function evaluateConfig(config, litNodes, wrong) {
        var lits = Object.keys(config)
        console.log(lits)
        console.log(litNodes)
        if (lits.length == litNodes.length) {
            // Validate Configuration
            var evalCheck = true
            for (var i = 0; i < lits.length; i++) {
                var lit
                var litValue
                if (lits[i].substr(0,3) == 'not') {
                    lit = lits[i].substr(3)
                    litValue = config[lits[i]]
                    for (var n = 0; n < lits.length; n++) {
                        if (lit == lits[n] && litValue == config[lits[n]]) {
                            evalCheck = false
                            if (!wrong.includes(lit)) {
                                wrong.push(lit)
                            }
                        }
                    }
                }
            }
            return evalCheck
        } else {
            return false
        }
    }

    function checkAnswer() {
        var total = 0
        var answers = document.querySelectorAll('.answer')
        for (var i = 0; i < answers.length; i++) {
            if (answers[i].textContent === 'T') {
                total += 1
            }
        }
        if (total == configurations.length) {
            changeFeedback('All cuts complete, congrats!')
            document.getElementById('userFeedbackTable').style="min-height: 300px; border: solid 1px green; width: 100%; text-align:left"
        }
    }


    svg.append('defs').append('marker')
    .attr('id', 'arrowhead')
    .attr('viewBox', '-0 -5 10 10')
    .attr('refX', 17)
    .attr('refY', 0)
    .attr('orient', 'auto')
    .attr('markerWidth', 6)
    .attr('markerHeight', 6)
    .attr('xoverflow', 'visible')
    .append('svg:path')
    .attr('d', 'M 0,-5 L 10 ,0 L 0,5')
    .attr('fill', '#999')
    .style('stroke','none');


    var simulation = d3.forceSimulation()
        .force("link", d3.forceLink().id(function (d) {return d.id;}).distance(5).strength(0.25))
        .force("charge", d3.forceManyBody().strength(-850))
        .force('y', d3.forceY().y(function(d) {
            return height/2
        }).strength(0.015))
        .force('x', d3.forceX().x(function(d){return 2 * width / 5}).strength(0.005))

    var link = svg.selectAll(".link")
    .data(links)
    .enter()
    .append("line")
    .attr("class", "link")
    .attr('marker-end','url(#arrowhead)')

    node = svg.selectAll(".node")
        .data(nodes)
        .enter()
        .append("g")
        .attr("class", function(d) {
            if (d.id === 'T' || d.id === 'F') {
                return "node stuck"
            } else {
                return "node unstuck"
            }
        }).attr('id', function(d) {
            if (d.id.length > 1) {
                return 'not' + d.id[d.id.length - 1]
            } else {
                return d.id
            }
        })
        .call(d3.drag()
                .on("start", dragstarted)
                .on("drag", dragged)
                // .on("end", dragended)
        )
        .on("click", function(d) {
            if (!(d.id === 'T' || d.id === 'F')) {
                d3.select(this).classed("stuck", d3.select(this).classed("stuck") ? false : true)
                d3.select(this).classed("unstuck", d3.select(this).classed("unstuck") ? false : true)
                toggleStick(d)
            }
          })
        .on('mouseover', function() {
            canMakeLine = false
        })
        .on('mouseout', function() {
            canMakeLine = true
        })

    node.append("circle")
        .attr("r", function(d) { return d.r })
        .style("fill", function (d, i) {
            if (d.id === 'T') {
                return 'lightgreen'
            } else if (d.id === 'F'){
                return 'red'
            } else {
                return 'lightblue'
            }
        })
        

    node.append("text")
        .attr("dy", 3)
        .attr('dx', -5)
        .text(function (d) {return d.id});

    simulation
        .nodes(nodes)
        .on("tick", ticked);

    simulation.force("link")
        .links(links);

    node.each(function(d) {
        if (d.id === 'T' || d.id === 'F') {
            d.fx = d.x
            d.fy = d.y
        }
    })
    
    function ticked() {
        link
            .attr("x1", function (d) {return d.source.x;})
            .attr("y1", function (d) {return d.source.y;})
            .attr("x2", function (d) {return d.target.x;})
            .attr("y2", function (d) {return d.target.y;});
        node
            .attr("transform", function (d) {return "translate(" + d.x + ", " + d.y + ")"})   
    }

    function dragstarted(d) {
        if (!d3.event.active) simulation.alphaTarget(0.3).restart()
    }

    function dragged(d) {
        if (d.fx) {
            d.fx = d3.event.x
            // d.fy = d3.event.y
        } else {
            d.x = d3.event.x;
            d.y = d3.event.y;
        }
    }

    function toggleStick(d) {
        if (d.fx) {
            d.fy = null
            d.fx = null
        } else {
            d.fx = d.x
            // d.fy = d.y
        }     
    }

    // FUNCTION USED TO ALTER THE TREE
    function highlightTree(values, lits) {

        for (var i = 0; i < lits.length; i++) {
            var node = d3.select('#' + lits[i])
            var not_node = d3.select('#not' + lits[i])
            
            if (values[i] === '1') {
                node.each(function(d) { 
                    d.category = 1
                })

                if (not_node) {
                    not_node.each(function(d) { 
                        d.category = 2
                        
                    })
                }
            } else {
                node.each(function(d) { 
                    d.category = 2
                })
                if (not_node) {
                    not_node.each(function(d) { 
                        d.category = 1
                    })
                }
            }
        }

        link.style('stroke', 'black')
        d3.selectAll('circle').style('fill', function(d) {
            if (d.id === 'T') {
                return 'lightgreen'
            } else if (d.id === 'F') {
                return 'red'
            } else {
                if (d.category === 1) {
                    return 'lightgreen'
                } else {
                    return 'red'
                }
            }
        })
    }

    function evaluateGraph() {
        if (simulation) {
            link.style('stroke', function(d) {
                if (d.source.category === d.target.category) {
                    return 'green'
                } else if (d.source.category < d.target.category) {
                    return 'red'
                } else {
                    return 'green'
                }
            })
        }
    }

    function removeAll() {
        var container = document.getElementById("truthtable")
        while (container.firstChild) {
            container.removeChild(container.firstChild)
        }
        var title_container = document.getElementById("tableTitle")
        while (title_container.firstChild) {
            title_container.removeChild(title_container.firstChild)
        }
        
    }

    function generate() {
        removeAll()
        // var imp_list = get_literals()
        console.log("Generate Table")
        var table = alter_table(produce_truth_table(countLiterals(imp_list)), imp_list)
        var container = document.getElementById("truthtable")
        var title_container = document.getElementById("tableTitle")
        var new_element = document.createElement("span")
        new_element.textContent = '\xa0\xa0'
        new_element.classList.add('table-title')
        for (var i = 0; i < table[0].length; i++) {
            new_element.textContent = new_element.textContent + table[0][i] + '\xa0\xa0\xa0'
        }
        title_container.appendChild(new_element)
        
        for (var i = 1; i < table.length; i++) {
            var new_element = document.createElement("span")
            new_element.classList.add('table-entry')
            new_element.classList.add('table-hover')
            new_element.textContent = '\xa0\xa0\xa0'
            for (var n = 0; n < table[i].length - 1; n++) {
                new_element.textContent = new_element.textContent + table[i][n] + '\xa0\xa0\xa0'
            }
            var br = document.createElement("br")
    
            new_element.addEventListener("click", function(e) {
                highlightTree(e)
            })
            
    
            container.appendChild(new_element)
    
            var answer = document.createElement('span')
            answer.classList.add('answer')
            answer.textContent = table[i][table[i].length - 1]
            container.appendChild(answer)
    
            container.appendChild(br)
        }
    }

    function checkPhysics() {
        if (document.getElementById('physics').checked) {
            var lit_sliders = document.querySelectorAll('.lit_toggle')
            var lit_inputs = []
            var lits = []
            for (var i = 0; i < lit_sliders.length; i++) {
                    var id_length = lit_sliders[i].id.length - 6
                    lits.push(lit_sliders[i].id.substring(0, id_length))
                    if (lit_sliders[i].checked) {
                        lit_inputs.push('1')
                    } else {
                        lit_inputs.push('0')
                    }
                
            }            
            
            highlightTree(lit_inputs, lits)
            simulation.force('y', d3.forceY().y(function(d) {
                return yCenters[d.category]
            }).strength(1))
            simulation.force("y").initialize(nodes)
            if (!document.querySelector('.cut')) {
                svg.append('line').attr('class', 'cut')
                .attr('x1', 0).attr('y1', height/2)
                .attr('x2', width).attr('y2', height/2)
                .attr('stroke-width', 1).attr('stroke', 'black')
                
                svg.append('text').attr('y', height/2 - 20).attr('x', 100).attr('class', 'cut-true').style('fill', 'green').text('True')
                svg.append('text').attr('y', height/2 + 30).attr('x', 100).attr('class', 'cut-false').style('fill', 'red').text('False')
            }

        } else {
            simulation.force('y', d3.forceY().y(function(d) {
                return height/2
            }).strength(0.015))
            simulation.force('y').initialize(nodes)

            d3.select('.cut').remove()
            d3.select('.cut-true').remove()
            d3.select('.cut-false').remove()
        }
    }

    function totalEvaluations() {
        var total = 0
        var answers = document.querySelectorAll('.answer')
        var states = [[document.getElementById('tableTitle').textContent]]
        for (var i = 0; i < answers.length; i++) {
            if (answers[i].textContent === 'T') {
                total += 1
                states.push(answers[i].previousElementSibling.textContent)
            }
        }
        document.getElementById('total-evaluations').textContent = total
        var statesHTML = document.getElementById('valid-states')
        statesHTML.textContent = states[0]
        // var br = document.createElement("br")
        // statesHTML.appendChild(br)
        for (var i = 1; i < states.length; i++) {
            var entry = document.createElement('div')
            entry.textContent = states[i]
            statesHTML.appendChild(entry)
            //statesHTML.appendChild(br)
        }

    }

    generate()
    document.getElementById("evaluateTreeButton").addEventListener("click", function() {
        evaluateGraph()
        if (document.querySelector('.activated')) {
            if (document.querySelector('.activated').nextElementSibling.textContent == 'T') {
                document.querySelector('.activated').className = 'table-entry correct'
            } else {
                document.querySelector('.activated').className = 'table-entry false'
            }
        }
    })

    document.getElementById('physics').addEventListener('change', function() {
        checkPhysics()
    })

    document.getElementById('totalButton').addEventListener('click', function() {
        totalEvaluations()
    })

    // Section where we append all of the user toggles used to change the state of each of the literals
    // var lit_list = countLiterals(get_literals())
    var lit_list = countLiterals(imp_list)
    var cont = document.getElementById('userInputTable')
    for (var i = 0; i < lit_list.length; i++) {
        var inp = document.createElement('span')
        var lit = document.createElement('span')
        lit.className = 'user-input-table py-1 px-3 ml-3'
        lit.textContent = lit_list[i]
        inp.appendChild(lit)
        var brE = document.createElement('br')
        var label = document.createElement('label')
        label.className = 'switch ml-3'
        var inp_two = document.createElement('input')
        inp_two.type = 'checkbox'
        inp_two.id = lit_list[i] + 'Toggle'
        inp_two.addEventListener('click', function() {
            changeInput()
        })
        inp_two.className = "lit_toggle"
        var span = document.createElement('span')
        span.className = 'slider-lit round'
        label.appendChild(inp_two)
        label.appendChild(span)
        inp.appendChild(label)
        cont.appendChild(inp)
        cont.appendChild(brE)
    }


    function changeInput() {
        var lit_sliders = document.querySelectorAll('.lit_toggle')
            var lit_inputs = []
            var lits = []
            for (var i = 0; i < lit_sliders.length; i++) {
                var id_length = lit_sliders[i].id.length - 6
                lits.push(lit_sliders[i].id.substring(0, id_length))
                if (lit_sliders[i].checked) {
                    lit_inputs.push('1')
                } else {
                    lit_inputs.push('0')
                } 
            }

        for (var i = 0; i < lits.length; i++) {
            var node = d3.select('#' + lits[i])
            var not_node = d3.select('#not' + lits[i])
            if (lit_inputs[i] === '1') {
                node.each(function(d) { 
                    d.category = 1
                })
                if (not_node) {
                    not_node.each(function(d) { 
                        d.category = 2
                        
                    })
                }
            } 
            else {
                node.each(function(d) { 
                    d.category = 2
                })
                if (not_node) {
                    not_node.each(function(d) { 
                        d.category = 1
                    })
                }
            }
        } 

        link.style('stroke', 'black')
        d3.selectAll('circle').style('fill', function(d) {
            if (d.id === 'T') {
                return 'lightgreen'
            } else if (d.id === 'F') {
                return 'red'
            } else {
                if (d.category === 1) {
                    return 'lightgreen'
                } else {
                    return 'red'
                }
            }
        })

        // This used to move the selected nodes when the toggle inputs were pressed
        if (document.getElementById('physics').checked) {
            simulation.force('y', d3.forceY().y(function(d) {
                return yCenters[d.category]
            }).strength(1))
            simulation.force("y").initialize(nodes)
        }
        
    }


    document.getElementById('physics').checked = false
    simulation.alphaTarget(0.3).restart()
}


function get_literals() {
    var inputs = document.querySelectorAll('.litInput')
    var imp_list = []
    for (var i = 0; i < inputs.length; i++) {
        var temp_list = inputs[i].value.trim().split("->")
        var corrected = []
        if (temp_list.length > 2) {
            alert("Please don't place more than 1 implication per input")
            return []
        } else {
            temp_list_2 = temp_list[0].split(' ').concat(temp_list[1].split(' '))
        }
        temp_list = []
        for (var n = 0; n < temp_list_2.length; n++) {
            if (!temp_list_2[n] == "") {
                temp_list.push(temp_list_2[n])
            }
        }
        if (temp_list.length > 2) {
            alert('Please only have two literals per input')
            return []
        }
        for (var n = 0; n < temp_list.length; n++) {
            if (!(temp_list[n] === '')) {
                corrected.push(temp_list[n])
            }
        }
        if (corrected.includes('T')){
            alert('Please do not use the literal T')
            return []
        } else if (corrected.includes('F')) {
            alert('Please do not use the literal F')
            return []
        } else {
            imp_list.push([corrected[0], corrected[corrected.length - 1]])
        }
        
    }
    return imp_list
}

// Function to check user inputs
function checkInputs() {
    console.log(document.querySelectorAll('.litInput'))
    return true
}
















// User Tree

document.onload = (function(d3, saveAs, Blob, undefined){
    "use strict";
  
    // TODO add user settings
    var consts = {
      defaultTitle: "literal"
    };
    var settings = {
      appendElSpec: "#graph"
    };
    // define graphcreator object
    var GraphCreator = function(svg, nodes, edges){
      var thisGraph = this;
          thisGraph.idct = 0;
  
      thisGraph.nodes = nodes || [];
      thisGraph.edges = edges || [];
  
      thisGraph.state = {
        selectedNode: null,
        selectedEdge: null,
        mouseDownNode: null,
        mouseDownLink: null,
        justDragged: false,
        justScaleTransGraph: false,
        lastKeyDown: -1,
        shiftNodeDrag: false,
        selectedText: null
      };
  
      // define arrow markers for graph links
      var defs = svg.append('svg:defs');
      defs.append('svg:marker')
        .attr('id', 'end-arrow')
        .attr('viewBox', '0 -5 10 10')
        .attr('refX', "32")
        .attr('markerWidth', 3.5)
        .attr('markerHeight', 3.5)
        .attr('orient', 'auto')
        .append('svg:path')
        .attr('d', 'M0,-5L10,0L0,5');
  
      // define arrow markers for leading arrow
      defs.append('svg:marker')
        .attr('id', 'mark-end-arrow')
        .attr('viewBox', '0 -5 10 10')
        .attr('refX', 7)
        .attr('markerWidth', 3.5)
        .attr('markerHeight', 3.5)
        .attr('orient', 'auto')
        .append('svg:path')
        .attr('d', 'M0,-5L10,0L0,5');
  
      thisGraph.svg = svg;
      thisGraph.svgG = svg.append("g")
            .classed(thisGraph.consts.graphClass, true);
      var svgG = thisGraph.svgG;
  
      // displayed when dragging between nodes
      thisGraph.dragLine = svgG.append('svg:path')
            .attr('class', 'link dragline hidden')
            .attr('d', 'M0,0L0,0')
            .style('marker-end', 'url(#mark-end-arrow)');
  
      // svg nodes and edges
      thisGraph.paths = svgG.append("g").selectAll("g");
      thisGraph.circles = svgG.append("g").selectAll("g");
  
      thisGraph.drag = d3.behavior.drag()
            .origin(function(d){
              return {x: d.x, y: d.y};
            })
            .on("drag", function(args){
              thisGraph.state.justDragged = true;
              thisGraph.dragmove.call(thisGraph, args);
            })
            .on("dragend", function() {
              // todo check if edge-mode is selected
            });
  
      // listen for key events
      d3.select(window).on("keydown", function(){
        thisGraph.svgKeyDown.call(thisGraph);
      })
      .on("keyup", function(){
        thisGraph.svgKeyUp.call(thisGraph);
      });
      svg.on("mousedown", function(d){thisGraph.svgMouseDown.call(thisGraph, d);});
      svg.on("mouseup", function(d){thisGraph.svgMouseUp.call(thisGraph, d);});
  
      // listen for dragging
      var dragSvg = d3.behavior.zoom()
            .on("zoom", function(){
              if (d3.event.sourceEvent.shiftKey){
                // TODO  the internal d3 state is still changing
                return false;
              } else{
                thisGraph.zoomed.call(thisGraph);
              }
              return true;
            })
            .on("zoomstart", function(){
              var ael = d3.select("#" + thisGraph.consts.activeEditId).node();
              if (ael){
                ael.blur();
              }
              if (!d3.event.sourceEvent.shiftKey) d3.select('body').style("cursor", "move");
            })
            .on("zoomend", function(){
              d3.select('body').style("cursor", "auto");
            });
  
      svg.call(dragSvg).on("dblclick.zoom", null);
  
      // listen for resize
      window.onresize = function(){thisGraph.updateWindow(svg);};
  
    };
  
    GraphCreator.prototype.setIdCt = function(idct){
      this.idct = idct;
    };
  
    GraphCreator.prototype.consts =  {
      selectedClass: "selected",
      connectClass: "connect-node",
      circleGClass: "conceptG",
      graphClass: "graph",
      activeEditId: "active-editing",
      BACKSPACE_KEY: 8,
      DELETE_KEY: 46,
      ENTER_KEY: 13,
      nodeRadius: 50
    };
  
    /* PROTOTYPE FUNCTIONS */
  
    GraphCreator.prototype.dragmove = function(d) {
      var thisGraph = this;
      if (thisGraph.state.shiftNodeDrag){
        thisGraph.dragLine.attr('d', 'M' + d.x + ',' + d.y + 'L' + d3.mouse(thisGraph.svgG.node())[0] + ',' + d3.mouse(this.svgG.node())[1]);
      } else{
        d.x += d3.event.dx;
        d.y +=  d3.event.dy;
        thisGraph.updateGraph();
      }
    };
  
    GraphCreator.prototype.deleteGraph = function(skipPrompt){
      var thisGraph = this,
          doDelete = true;
      if (!skipPrompt){
        doDelete = window.confirm("Press OK to delete this graph");
      }
      if(doDelete){
        thisGraph.nodes = [];
        thisGraph.edges = [];
        thisGraph.updateGraph();
      }
    };
  
    /* select all text in element: taken from http://stackoverflow.com/questions/6139107/programatically-select-text-in-a-contenteditable-html-element */
    GraphCreator.prototype.selectElementContents = function(el) {
      var range = document.createRange();
      range.selectNodeContents(el);
      var sel = window.getSelection();
      sel.removeAllRanges();
      sel.addRange(range);
    };
  
  
    /* insert svg line breaks: taken from http://stackoverflow.com/questions/13241475/how-do-i-include-newlines-in-labels-in-d3-charts */
    GraphCreator.prototype.insertTitleLinebreaks = function (gEl, title) {
      var words = title.split(/\s+/g),
          nwords = words.length;
      var el = gEl.append("text")
            .attr("text-anchor","middle")
            .attr("dy", "-" + (nwords-1)*7.5);
  
      for (var i = 0; i < words.length; i++) {
        var tspan = el.append('tspan').text(words[i]);
        if (i > 0)
          tspan.attr('x', 0).attr('dy', '15');
      }
    };
  
  
    // remove edges associated with a node
    GraphCreator.prototype.spliceLinksForNode = function(node) {
      var thisGraph = this,
          toSplice = thisGraph.edges.filter(function(l) {
        return (l.source === node || l.target === node);
      });
      toSplice.map(function(l) {
        thisGraph.edges.splice(thisGraph.edges.indexOf(l), 1);
      });
    };
  
    GraphCreator.prototype.replaceSelectEdge = function(d3Path, edgeData){
      var thisGraph = this;
      d3Path.classed(thisGraph.consts.selectedClass, true);
      if (thisGraph.state.selectedEdge){
        thisGraph.removeSelectFromEdge();
      }
      thisGraph.state.selectedEdge = edgeData;
    };
  
    GraphCreator.prototype.replaceSelectNode = function(d3Node, nodeData){
      var thisGraph = this;
      d3Node.classed(this.consts.selectedClass, true);
      if (thisGraph.state.selectedNode){
        thisGraph.removeSelectFromNode();
      }
      thisGraph.state.selectedNode = nodeData;
    };
  
    GraphCreator.prototype.removeSelectFromNode = function(){
      var thisGraph = this;
      thisGraph.circles.filter(function(cd){
        return cd.id === thisGraph.state.selectedNode.id;
      }).classed(thisGraph.consts.selectedClass, false);
      thisGraph.state.selectedNode = null;
    };
  
    GraphCreator.prototype.removeSelectFromEdge = function(){
      var thisGraph = this;
      thisGraph.paths.filter(function(cd){
        return cd === thisGraph.state.selectedEdge;
      }).classed(thisGraph.consts.selectedClass, false);
      thisGraph.state.selectedEdge = null;
    };
  
    GraphCreator.prototype.pathMouseDown = function(d3path, d){
      var thisGraph = this,
          state = thisGraph.state;
      d3.event.stopPropagation();
      state.mouseDownLink = d;
  
      if (state.selectedNode){
        thisGraph.removeSelectFromNode();
      }
  
      var prevEdge = state.selectedEdge;
      if (!prevEdge || prevEdge !== d){
        thisGraph.replaceSelectEdge(d3path, d);
      } else{
        thisGraph.removeSelectFromEdge();
      }
    };
  
    // mousedown on node
    GraphCreator.prototype.circleMouseDown = function(d3node, d){
      var thisGraph = this,
          state = thisGraph.state;
      d3.event.stopPropagation();
      state.mouseDownNode = d;
      if (d3.event.shiftKey){
        state.shiftNodeDrag = d3.event.shiftKey;
        // reposition dragged directed edge
        thisGraph.dragLine.classed('hidden', false)
          .attr('d', 'M' + d.x + ',' + d.y + 'L' + d.x + ',' + d.y);
        return;
      }
    };
  
    /* place editable text on node in place of svg text */
    GraphCreator.prototype.changeTextOfNode = function(d3node, d){
      var thisGraph= this,
          consts = thisGraph.consts,
          htmlEl = d3node.node();
      d3node.selectAll("text").remove();
      var nodeBCR = htmlEl.getBoundingClientRect(),
          curScale = nodeBCR.width/consts.nodeRadius,
          placePad  =  50*curScale,
          useHW = curScale > 1 ? nodeBCR.width*0.71 : consts.nodeRadius*1.42;
      // replace with editableconent text
      var d3txt = thisGraph.svg.selectAll("foreignObject")
            .data([d])
            .enter()
            .append("foreignObject")
            .attr("x", nodeBCR.left - 2.8*placePad)
            .attr("y", nodeBCR.top - 230 - curScale)
            .attr("height", 2*useHW)
            .attr("width", useHW)
            .append("xhtml:p")
            .attr("id", consts.activeEditId)
            .attr("contentEditable", "true")
            .text(d.title)
            .on("mousedown", function(d){
              d3.event.stopPropagation();
            })
            .on("keydown", function(d){
              d3.event.stopPropagation();
              if (d3.event.keyCode == consts.ENTER_KEY && !d3.event.shiftKey){
                this.blur();
              }
            })
            .on("blur", function(d){
              d.title = this.textContent;
              thisGraph.insertTitleLinebreaks(d3node, d.title);
              d3.select(this.parentElement).remove();
            });
      return d3txt;
    };
  
    // mouseup on nodes
    GraphCreator.prototype.circleMouseUp = function(d3node, d){
      var thisGraph = this,
          state = thisGraph.state,
          consts = thisGraph.consts;
      // reset the states
      state.shiftNodeDrag = false;
      d3node.classed(consts.connectClass, false);
  
      var mouseDownNode = state.mouseDownNode;
  
      if (!mouseDownNode) return;
  
      thisGraph.dragLine.classed("hidden", true);
  
      if (mouseDownNode !== d){
        // we're in a different node: create new edge for mousedown edge and add to graph
        var newEdge = {source: mouseDownNode, target: d};
        var filtRes = thisGraph.paths.filter(function(d){
          if (d.source === newEdge.target && d.target === newEdge.source){
            thisGraph.edges.splice(thisGraph.edges.indexOf(d), 1);
          }
          return d.source === newEdge.source && d.target === newEdge.target;
        });
        if (!filtRes[0].length){
          thisGraph.edges.push(newEdge);
          thisGraph.updateGraph();
        }
      } else{
        // we're in the same node
        if (state.justDragged) {
          // dragged, not clicked
          state.justDragged = false;
        } else{
          // clicked, not dragged
          if (d3.event.shiftKey){
            // shift-clicked node: edit text content
            var d3txt = thisGraph.changeTextOfNode(d3node, d);
            var txtNode = d3txt.node();
            thisGraph.selectElementContents(txtNode);
            txtNode.focus();
          } else{
            if (state.selectedEdge){
              thisGraph.removeSelectFromEdge();
            }
            var prevNode = state.selectedNode;
  
            if (!prevNode || prevNode.id !== d.id){
              thisGraph.replaceSelectNode(d3node, d);
            } else{
              thisGraph.removeSelectFromNode();
            }
          }
        }
      }
      state.mouseDownNode = null;
      return;
  
    }; // end of circles mouseup
  
    // mousedown on main svg
    GraphCreator.prototype.svgMouseDown = function(){
      this.state.graphMouseDown = true;
    };
  
    // mouseup on main svg
    GraphCreator.prototype.svgMouseUp = function(){
      var thisGraph = this,
          state = thisGraph.state;
      if (state.justScaleTransGraph) {
        // dragged not clicked
        state.justScaleTransGraph = false;
      } else if (state.graphMouseDown && d3.event.shiftKey){
        // clicked not dragged from svg
        var xycoords = d3.mouse(thisGraph.svgG.node()),
            d = {id: thisGraph.idct++, title: consts.defaultTitle, x: xycoords[0], y: xycoords[1]};
        thisGraph.nodes.push(d);
        thisGraph.updateGraph();
        // make title of text immediently editable
        var d3txt = thisGraph.changeTextOfNode(thisGraph.circles.filter(function(dval){
          return dval.id === d.id;
        }), d),
            txtNode = d3txt.node();
        thisGraph.selectElementContents(txtNode);
        txtNode.focus();
      } else if (state.shiftNodeDrag){
        // dragged from node
        state.shiftNodeDrag = false;
        thisGraph.dragLine.classed("hidden", true);
      }
      state.graphMouseDown = false;
    };
  
    // keydown on main svg
    GraphCreator.prototype.svgKeyDown = function() {
      var thisGraph = this,
          state = thisGraph.state,
          consts = thisGraph.consts;
      // make sure repeated key presses don't register for each keydown
      if(state.lastKeyDown !== -1) return;
  
      state.lastKeyDown = d3.event.keyCode;
      var selectedNode = state.selectedNode,
          selectedEdge = state.selectedEdge;
  
      switch(d3.event.keyCode) {
      case consts.BACKSPACE_KEY:
      case consts.DELETE_KEY:
        d3.event.preventDefault();
        if (selectedNode){
          thisGraph.nodes.splice(thisGraph.nodes.indexOf(selectedNode), 1);
          thisGraph.spliceLinksForNode(selectedNode);
          state.selectedNode = null;
          thisGraph.updateGraph();
        } else if (selectedEdge){
          thisGraph.edges.splice(thisGraph.edges.indexOf(selectedEdge), 1);
          state.selectedEdge = null;
          thisGraph.updateGraph();
        }
        break;
      }
    };
  
    GraphCreator.prototype.svgKeyUp = function() {
      this.state.lastKeyDown = -1;
    };
  
    // call to propagate changes to graph
    GraphCreator.prototype.updateGraph = function(){
  
      var thisGraph = this,
          consts = thisGraph.consts,
          state = thisGraph.state;
  
      thisGraph.paths = thisGraph.paths.data(thisGraph.edges, function(d){
        return String(d.source.id) + "+" + String(d.target.id);
      });
      var paths = thisGraph.paths;
      // update existing paths
      paths.style('marker-end', 'url(#end-arrow)')
        .classed(consts.selectedClass, function(d){
          return d === state.selectedEdge;
        })
        .attr("d", function(d){
          return "M" + d.source.x + "," + d.source.y + "L" + d.target.x + "," + d.target.y;
        });
  
      // add new paths
      paths.enter()
        .append("path")
        .style('marker-end','url(#end-arrow)')
        .classed("link", true)
        .attr("d", function(d){
          return "M" + d.source.x + "," + d.source.y + "L" + d.target.x + "," + d.target.y;
        })
        .on("mousedown", function(d){
          thisGraph.pathMouseDown.call(thisGraph, d3.select(this), d);
          }
        )
        .on("mouseup", function(d){
          state.mouseDownLink = null;
        });
  
      // remove old links
      paths.exit().remove();
  
      // update existing nodes
      thisGraph.circles = thisGraph.circles.data(thisGraph.nodes, function(d){ return d.id;});
      thisGraph.circles.attr("transform", function(d){return "translate(" + d.x + "," + d.y + ")";});
  
      // add new nodes
      var newGs= thisGraph.circles.enter()
            .append("g");
  
      newGs.classed(consts.circleGClass, true)
        .attr("transform", function(d){return "translate(" + d.x + "," + d.y + ")";})
        .on("mouseover", function(d){
          if (state.shiftNodeDrag){
            d3.select(this).classed(consts.connectClass, true);
          }
        })
        .on("mouseout", function(d){
          d3.select(this).classed(consts.connectClass, false);
        })
        .on("mousedown", function(d){
          thisGraph.circleMouseDown.call(thisGraph, d3.select(this), d);
        })
        .on("mouseup", function(d){
          thisGraph.circleMouseUp.call(thisGraph, d3.select(this), d);
        })
        .call(thisGraph.drag);
  
      newGs.append("circle")
        .attr("r", String(consts.nodeRadius));
  
      newGs.each(function(d){
        thisGraph.insertTitleLinebreaks(d3.select(this), d.title);
      });
  
      // remove old nodes
      thisGraph.circles.exit().remove();

      document.getElementById('generateTreeButton').addEventListener('click', function() {
        var graph = thisGraph
        var imp_list = []
        var literals = []
        evaluation(graph)
      })

    };
  
    GraphCreator.prototype.zoomed = function(){
      this.state.justScaleTransGraph = true;
      d3.select("." + this.consts.graphClass)
        .attr("transform", "translate(" + d3.event.translate + ") scale(" + d3.event.scale + ")");
    };
  
    GraphCreator.prototype.updateWindow = function(svg){
      var docEl = document.documentElement,
          bodyEl = document.getElementsByTagName('body')[0];
      var x = window.innerWidth || docEl.clientWidth || bodyEl.clientWidth;
      var y = window.innerHeight|| docEl.clientHeight|| bodyEl.clientHeight;
      svg.attr("width", x).attr("height", y);
    };
  
    
    
  
  
    /**** MAIN ****/
  
    // warn the user when leaving
    // window.onbeforeunload = function(){
    //   return "Make sure to save your graph locally before leaving :-)";
    // };
  
    var docEl = document.documentElement,
        bodyEl = document.getElementsByTagName('body')[0];
  
    // var width = window.innerWidth || docEl.clientWidth || bodyEl.clientWidth,
    //     height =  window.innerHeight|| docEl.clientHeight|| bodyEl.clientHeight;
    var width = window.innerWidth/12 * 9.5,
        height = 550
  
    var xLoc = width/2 - 25,
        yLoc = 100;
  
    // initial node data
    var nodes = [];
    var edges = [];

    
  
  
    /** MAIN SVG **/
    var svg = d3.select(settings.appendElSpec).append("svg")
          .attr("width", width)
          .attr("height", height);
    var graph = new GraphCreator(svg, nodes, edges);
        graph.setIdCt(2);
    graph.updateGraph();
  }(window.d3, window.saveAs, window.Blob))


var imp_list = []
var literals = []

function evaluation(graph) {
    try {
        // How to get the title of each node
        var nodeTitles = d3.select('svg').selectAll('text')[0]
        for (var i = 0; i < nodeTitles.length; i++) {
            literals.push(nodeTitles[i].textContent)
        }

        var nodePaths = graph.edges
        for (var i = 0; i < nodePaths.length; i++) {
        imp_list.push([nodePaths[i].source.title, nodePaths[i].target.title])
        }

        if (isUserTreeValid(produceUserTree(imp_list, literals), combine_tree_pairs(new_join_nodes(create_nodes(get_literals()))))) {
            while(document.getElementById('graph').firstChild) {
                document.getElementById('graph').removeChild(document.getElementById('graph').firstChild)
            }
                
            changeFeedback('Tree is correct! Continue onto next exercise.')
            setCookie('exercise5', '1', 7)
            

        } else {
            console.log('INCORRECT!!!')
            imp_list = []
            literals = []
        }
    }
    catch {
        console.log('Overrun')
    }
  

}

function checkCycles(tree) {
    var virtual_tree = createDictTree(tree)

    for (var i = 0; i < tree.length; i++) {
        var cyclic_lit = tree[i].nood
        var child_nodes = []
        for (var n = 0; n < tree[i].children.length; n++) {
            var temp_list = []
            temp_list.push(tree[i].children[n])
            child_nodes.push(temp_list)
        }
        var counter = 0
        outer:
        while (child_nodes.length > 0) {

            for (var n = 0; n < child_nodes.length; n++) {
                if (child_nodes[n][child_nodes[n].length - 1] == cyclic_lit) {
                    return child_nodes[n]
                }

                if (hasDuplicates(child_nodes[n])) {
                    break outer
                }
                console.log('VIRTUAL TREE!!!')
                console.log(virtual_tree)
                try {
                    if (virtual_tree[child_nodes[n][child_nodes[n].length - 1]].children.length > 0) {
                        var temp_branch = child_nodes[n]
                        child_nodes.splice(n, n + 1)
                        for (var j = 0; j < virtual_tree[temp_branch[temp_branch.length - 1]].children.length; j++) {
                            var temp_temp_branch = temp_branch.slice()
                            temp_temp_branch.push(virtual_tree[temp_branch[temp_branch.length - 1]].children[j])
                            child_nodes.push(temp_temp_branch)
                        }
                        
                    } else {
                        child_nodes.splice(n, n + 1)
                    }
                } catch {
                    child_nodes.splice(n, n + 1)
                }
                
            }
        }
    }
    return false
}

function changeTreeForCycles(tree) {
    
    var cycle = checkCycles(tree)
    if (cycle) {
        var virtual_tree = createDictTree(tree)
        var title = cycle.join('-')

        var node = {
            nood: title,
            parents: [],
            children: []
        }
        for (var i = 0; i < cycle.length; i++) {
            for (var n = 0; n < virtual_tree[cycle[i]].parents.length; n++) {
                if (!cycle.includes(virtual_tree[cycle[i]].parents[n])) {
                    node.parents.push(virtual_tree[cycle[i]].parents[n])
                }
                
            }
            for (var n = 0; n < virtual_tree[cycle[i]].children.length; n++) {
                if (!cycle.includes(virtual_tree[cycle[i]].children[n])) {
                    node.children.push(virtual_tree[cycle[i]].children[n])
                }
            }
        }
        for (var i = 0; i < tree.length; i++) {
            console.log(tree[i].nood)
            if (cycle.includes(tree[i].nood)) {
                console.log(`Removing node: ${tree[i].nood}`)
                tree.splice(i, i+1)
                i--
            } else {
                virtual_tree = createDictTree(tree)
                var temp_node = tree[i]
                var occur = false
                for (var n = 0; n < temp_node.children.length; n++) {
                    if (cycle.includes(temp_node.children[n])) {
                        temp_node.children.splice(n, n+1)
                        console.log(`Removing child: ${temp_node.children[n]} from node: ${tree[i].nood}`)
                        n--
                        occur = true
                    }
                }
                if (occur) {
                    temp_node.children.push(title)
                }
                occur = false
                for (var n = 0; n < temp_node.parents.length; n++) {
                    if (cycle.includes(temp_node.parents[n])) {
                        console.log(`Removing parent: ${temp_node.parents[n]} from node: ${tree[i].nood}`)
                        temp_node.parents.splice(n, n+1)
                        n--
                        occur = true
                    }
                }
                if (occur) {
                    temp_node.parents.push(title)
                }
            }
        }
        tree.push(node)
        appendFeedback(`Combined literals: [${cycle}] to make '${title}', as they form a cycle. `)
        return changeTreeForCycles(tree)
    } else {
        return tree
    }
}



function isReferenced(tree_one, tree_two) {
    var crossover = list_literals(get_literals())
    parents_children = []
    for (var i = 0; i < tree_one.length; i++) {
        for (var n = 0; n < tree_one[i].children.length; n++) {
            parents_children.push(tree_one[i].children[n])
        }
        for (var n = 0; n < tree_one[i].parents.length; n++) {
            parents_children.push(tree_one[i].parents[n])
        }
    }
    var tree_one_nodes = []
    for (var i = 0; i < tree_one.length; i++) {
        tree_one_nodes.push(tree_one[i].nood)
    }
    var tree_two_nodes = []
    for (var i = 0; i < tree_two.length; i++) {
        tree_two_nodes.push(tree_two[i].nood)
    }

    for (var i = 0; i < tree_two.length; i++) {
        if (parents_children.includes(tree_two[i].nood)) {
            return true
        }
    }

    for (var i = 0; i < crossover.length; i++) {
        if (tree_one_nodes.includes(crossover[i][0]) && tree_two_nodes.includes(crossover[i][1])) {
            return true
        } else if (tree_one_nodes.includes(crossover[i][1]) && tree_two_nodes.includes(crossover[i][0])) {
            return true
        }
    }
    return false
}

// Function which returns whether a given array has duplicates
function hasDuplicates(array) {
    return (new Set(array)).size !== array.length
}


// This function needs to be editted for further user feedback!!!
function isUserTreeValid(tree, combined_trees) {
    var all_lits = countLiterals(get_literals())
    for (var i = 0; i < tree.length; i++) {
        var temp_lit = ''
        if (tree[i].nood.startsWith('!')) {
            temp_lit = not_literal(tree[i].nood)
        } else {
            temp_lit = tree[i].nood
        }
        if (!all_lits.includes(temp_lit)) {
            changeFeedback(`Remove node '${tree[i].nood}'`)
            return false
        }
    }
    var occurs = false
    var feedback = ''
    console.log('Combined trees:')
    console.log(combined_trees)
    for (var i = 0; i < combined_trees.length; i++) {
        console.log(`checking for tree:`)
        console.log(combined_trees[i])
        var trees = combined_trees[i]
        if (trees.length > 1) {
            if(isReferenced(trees[0], trees[1])) {
                var temp_tree = trees[0]
                for (var n = 0; n < temp_tree.length; n++) {
                    occurs = false
                    temp_node = identifyNode(temp_tree[n])
                    for (var j = 0; j < tree.length; j++) {
                        if (temp_tree[n].nood === tree[j].nood) {
                            if (temp_node === identifyNode(tree[j])) {
                                occurs = true
                                break
                            } else {
                                changeFeedback(findFeedback(temp_tree[n], tree[j], feedback))
                                return false
                            }
                        }
                    }
                    if (!occurs) {
                        changeFeedback(feedback + `Please add a node for: '${temp_tree[n].nood}'`)
                        return false
                    }
                }

                var temp_tree = trees[1]
                for (var n = 0; n < temp_tree.length; n++) {
                    occurs = false
                    temp_node = identifyNode(temp_tree[n])
                    for (var j = 0; j < tree.length; j++) {
                        if (temp_tree[n].nood === tree[j].nood) {
                            if (temp_node === identifyNode(tree[j])) {
                                occurs = true
                                break
                            } else {
                                changeFeedback(findFeedback(temp_tree[n], tree[j], feedback))
                                return false
                            }
                        }
                        
                    }
                    if (!occurs) {
                        changeFeedback(feedback + `Please add a node for: '${temp_tree[n].nood}'`)
                        return false
                    }
                }
            } else {
                var temp_tree = trees[0]
                var once_occured = false
                for (var n = 0; n < temp_tree.length; n++) {
                    occurs = false
                    temp_node = identifyNode(temp_tree[n])
                    for (var j = 0; j < tree.length; j++) {
                        if (temp_tree[n].nood === tree[j].nood) {
                            once_occured = true
                            if (temp_node === identifyNode(tree[j])) {
                                occurs = true
                                break
                            } else {
                                changeFeedback(findFeedback(temp_tree[n], tree[j], feedback))
                                return false
                            }
                        }
                        
                    }
                    if (!occurs) {
                        break
                    }
                        
                }

                if (!once_occured) {
                    var temp_tree = trees[1]
                    for (var n = 0; n < temp_tree.length; n++) {
                        occurs = false
                        temp_node = identifyNode(temp_tree[n])
                        for (var j = 0; j < tree.length; j++) {
                            if (temp_tree[n].nood === tree[j].nood) {
                                if (temp_node === identifyNode(tree[j])) {
                                    occurs = true
                                    break
                                } else {
                                    changeFeedback(findFeedback(temp_tree[n], tree[j], feedback))
                                    return false
                                }
                            }
                            
                        }
                        if (!occurs) {
                            changeFeedback(feedback + `Please add a node for: '${temp_tree[n].nood}'`)
                            return false
                        }
                    }
                    var other_tree_nodes = []
                    for (var k = 0; k < trees[0].length; k++) {
                        other_tree_nodes.push(trees[0][k].nood)
                    }
                    for (var k = 0; k < tree.length; k++) {
                        if (other_tree_nodes.includes(tree[k].nood)) {
                            changeFeedback(`Remove node '${tree[k].nood}'`)
                            return false
                        }
                    }
                } else {
                    var other_tree_nodes = []
                    for (var k = 0; k < trees[1].length; k++) {
                        other_tree_nodes.push(trees[1][k].nood)
                    }
                    for (var k = 0; k < tree.length; k++) {
                        if (other_tree_nodes.includes(tree[k].nood)) {
                            changeFeedback(`Remove node '${tree[k].nood}'`)
                            return false
                        }
                    }                    
                }
            }
        } else {
            var temp_tree = trees[0]
            for (var n = 0; n < temp_tree.length; n++) {
                occurs = false
                temp_node = identifyNode(temp_tree[n])
                for (var j = 0; j < tree.length; j++) {
                    if (temp_tree[n].nood === tree[j].nood) {
                        if (temp_node === identifyNode(tree[j])) {
                            occurs = true
                            break
                        } else {
                            changeFeedback(findFeedback(temp_tree[n], tree[j], feedback))
                            return false
                        }
                    }
                    
                }
                if (!occurs) {
                    changeFeedback(feedback + `Please add a node for: '${temp_tree[n].nood}'`)
                    return false
                }
            }
        }
    }
    changeFeedback('The Tree is correct :)')
    return true
    
}

function findFeedback(correct_node, user_node, feedback) {
    var missing_children = []
    for (var i = 0; i < correct_node.children.length; i++) {
        if (!user_node.children.includes(correct_node.children[i])) {
            missing_children.push(correct_node.children[i])
        }
    }

    var missing_parents = []
    for (var i = 0; i < correct_node.parents.length; i++) {
        if (!user_node.parents.includes(correct_node.parents[i])) {
            missing_parents.push(correct_node.parents[i])
        }
    }

    if (missing_children.length > 0) {
        feedback = feedback + `The node ${user_node.nood} is missing arrows to: '${missing_children}'`
        if (missing_parents.length > 0) {
            feedback = feedback + `, and is missing arrows from '${missing_parents}'.`
        } else {
            feedback = feedback + '. '
        }
    } else {
        if (missing_parents.length > 0) {
            feedback = feedback + `The node ${user_node.nood} is missing arrows from '${missing_parents}'.`
        } else {
            var invalid_connection = []
            for (var i = 0; i < user_node.children.length; i++) {
                if (!correct_node.children.includes(user_node.children[i]) && !invalid_connection.includes(user_node.children[i])) {
                    invalid_connection.push(user_node.children[i])
                }
            }
            if (invalid_connection.length > 0) {
                feedback = `Remove connection from '${user_node.nood}' to '${invalid_connection}'`
            } else {
                for (var i = 0; i < user_node.parents.length; i++) {
                    if (!correct_node.parents.includes(user_node.parents[i]) && !invalid_connection.includes(user_node.parents[i])) {
                        invalid_connection.push(user_node.parents[i])
                    }
                }
                feedback = `Remove connection from '${invalid_connection}' to '${user_node.nood}'`
            }
            
        }
    }

    return feedback
}


// Function for return unique code based on node composition
function identifyNode(node) {
    var output = ''
    output = output + node.nood
    output = output + 'c'

    var temp_num = 0
    for (var i = 0; i < node.children.length; i++) {
        temp_num += node.children[i].charCodeAt(0)
    }
    output = output + String(temp_num)

    output = output + 'p'
    temp_num = 0
    for (var i = 0; i < node.parents.length; i++) {
        temp_num += node.parents[i].charCodeAt(0)
    }
    output = output + String(temp_num)
    return output
}

function list_literals(imp_list) {
    output = []
    for (var i = 0; i < imp_list.length; i++) {
        if (!output.includes(imp_list[i][0])) {
            output.push(imp_list[i][0])
        }
        if (!output.includes(imp_list[i][1])) {
            output.push(imp_list[i][1])
        }
    }
    var final_output = []
    var final_final_output = []
    for (var i = 0; i < output.length; i++) {
        var temp_lit = not_literal(output[i])
        if (output.includes(temp_lit)) {
            if (!final_output.includes(temp_lit)) {
                final_output.push(temp_lit)
                final_output.push(output[i])
                final_final_output.push([temp_lit, output[i]])
            }
        }
    }
    return final_final_output
}

// Function for producing a dictionary that represents the virtual tree
function createDictTree(tree) {
    var output = {}
    for (var i = 0; i < tree.length; i++) {
        output[tree[i].nood] = tree[i]
    }
    return output
}

function changeFeedback(str) {
    document.getElementById('userFeedbackTable').textContent = str
}

function appendFeedback(str) {
    document.getElementById('userFeedbackTable').textContent = document.getElementById('userFeedbackTable').textContent + str
}


// HELPER FUNCTION TO BE IGNORED
function isEqual(value, other) {

	// Get the value type
	var type = Object.prototype.toString.call(value);

	// If the two objects are not the same type, return false
	if (type !== Object.prototype.toString.call(other)) return false;

	// If items are not an object or array, return false
	if (['[object Array]', '[object Object]'].indexOf(type) < 0) return false;

	// Compare the length of the length of the two items
	var valueLen = type === '[object Array]' ? value.length : Object.keys(value).length;
	var otherLen = type === '[object Array]' ? other.length : Object.keys(other).length;
	if (valueLen !== otherLen) return false;

	// Compare two items
	var compare = function (item1, item2) {

		// Get the object type
		var itemType = Object.prototype.toString.call(item1);

		// If an object or array, compare recursively
		if (['[object Array]', '[object Object]'].indexOf(itemType) >= 0) {
			if (!isEqual(item1, item2)) return false;
		}

		// Otherwise, do a simple comparison
		else {

			// If the two items are not the same type, return false
			if (itemType !== Object.prototype.toString.call(item2)) return false;

			// Else if it's a function, convert to a string and compare
			// Otherwise, just compare
			if (itemType === '[object Function]') {
				if (item1.toString() !== item2.toString()) return false;
			} else {
				if (item1 !== item2) return false;
			}

		}
	};

	// Compare properties
	if (type === '[object Array]') {
		for (var i = 0; i < valueLen; i++) {
			if (compare(value[i], other[i]) === false) return false;
		}
	} else {
		for (var key in value) {
			if (value.hasOwnProperty(key)) {
				if (compare(value[key], other[key]) === false) return false;
			}
		}
	}

	// If nothing failed, return true
	return true;

}; 

function setCookie(name,value,days) {
    var expires = "";
    if (days) {
        var date = new Date();
        date.setTime(date.getTime() + (days*24*60*60*1000));
        expires = "; expires=" + date.toUTCString();
    }
    document.cookie = name + "=" + (value || "")  + expires + "; path=/";
}