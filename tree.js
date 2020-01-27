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

function new_join_nodes(nodes_object) {
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

    var validStates = document.getElementById('valid-states')
    while (validStates.firstChild) {
        validStates.removeChild(validStates.firstChild)
    }

    var userInput = document.getElementById('userInputTable')
    while (userInput.firstChild) {
        userInput.removeChild(userInput.firstChild)
    }

    document.getElementById('total-evaluations').textContent = ''

    var width = 1550,
        height = 700

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
        y: height + 30,
        r: 20,
        category: 2
    })


    // Append the svg element
    var colors = d3.scaleOrdinal(d3.schemeCategory20);
    var yCenters = [375, 187.5, 565.5]

    var svg = d3.select("#graph").append("svg")
    .attr("preserveAspectRatio", "xMinYMin meet")
    .attr("viewBox", "0 0 1200 750")
    // .call(d3.zoom().on("zoom", function () {
    //     svg.attr("transform", d3.event.transform)
    // })).append('g')


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
        .force("charge", d3.forceManyBody().strength(-650))
        .force('y', d3.forceY().y(function(d) {
            return height/2
        }).strength(0.015))
        .force('x', d3.forceX().x(function(d){return 2 * width / 5}).strength(0.05))

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
        var imp_list = get_literals()
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
    var lit_list = countLiterals(get_literals())
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

    document.getElementById('unstickAllButton').addEventListener('click', function() {
        unstickAll()
    })

    function unstickAll() {
        d3.selectAll('.node').each(function(d) {
            if (!(d.id === 'T' || d.id === 'F')) {
                d3.select(this).classed("stuck", d3.select(this).classed("stuck") ? false : false)
                d3.select(this).classed("unstuck", d3.select(this).classed("unstuck") ? true : true)
                unstickNode(d)
            }
        })
    }

    function unstickNode(d) {
        if (d.fx) {
            d.fx = null
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

var treeState = 0

document.getElementById("generateTreeButton").addEventListener("click", function() {
    if (treeState) {
        // generateTree(produce_valid_trees(combine_tree_pairs(new_join_nodes(create_nodes(get_literals())))))
        // document.getElementById("right-side").style = "display: block"
        // document.getElementById("answers").style = "display: block"
    } else {
        userTree(d3, saveAs, Blob, undefined)
        console.log('Begin Drawing')
        treeState = 1
    }
    
})



















// User Tree

function userTree(d3, saveAs, Blob, undefined){
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
          placePad  =  5*curScale,
          useHW = curScale > 1 ? nodeBCR.width*0.71 : consts.nodeRadius*1.42;
      // replace with editableconent text
      var d3txt = thisGraph.svg.selectAll("foreignObject")
            .data([d])
            .enter()
            .append("foreignObject")
            .attr("x", nodeBCR.left )
            .attr("y", nodeBCR.top - 50)
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
  
    var width = window.innerWidth || docEl.clientWidth || bodyEl.clientWidth,
        height =  window.innerHeight|| docEl.clientHeight|| bodyEl.clientHeight;
  
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
  }(window.d3, window.saveAs, window.Blob);

function evaluation(graph) {
    try {
        // How to get the title of each node
        var literals = []
        var nodeTitles = d3.select('svg').selectAll('text')[0]
        for (var i = 0; i < nodeTitles.length; i++) {
        literals.push(nodeTitles[i].textContent)
        }
        console.log(literals)

        var imp_list = []
        var nodePaths = graph.edges
        for (var i = 0; i < nodePaths.length; i++) {
        imp_list.push([nodePaths[i].source.title, nodePaths[i].target.title])
        }
        console.log(imp_list)

        while(document.getElementById('graph').firstChild) {
        document.getElementById('graph').removeChild(document.getElementById('graph').firstChild)
        }

        var script = document.createElement('script');
        script.onload = function () {
          generateTree(produce_valid_trees(combine_tree_pairs(new_join_nodes(create_nodes(imp_list)))))
          document.getElementById("right-side").style = "display: block"
          document.getElementById("answers").style = "display: block"
        };
        script.src = "https://d3js.org/d3.v4.min.js";

        document.head.appendChild(script);
    }
    catch {
        console.log('Overrun')
    }
  

}
        